import CoInd.M
import CoInd.Paco
import CoInd.Tactic
import CoInd.Container
import CoInd.Utils
import CoInd.Eqns
import CoInd.Std.DelabRule
import CoInd.CPO


import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Monotonicity.Basic

import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq

universe u v w u₀ u₁ u₂

variable {α : Type u}

#print Container
#print Container.Obj

inductive Kahn.A (α: Type u) where
| cons : α → Kahn.A α
| bot

def Kahn.B {α: Type u} : Kahn.A α → Type u
| .cons _ => PUnit
| _ => PEmpty

def Kahn.C (α: Type u) : Container := ⟨A α, Kahn.B⟩

inductive Kahn.F (α: Type u) (β: Type v) where
| cons : α → β → F α β
| bot : F α β

instance [Inhabited β] : Inhabited (Kahn.F α β) where
  default := .bot

def Kahn (α: Type u) : Type u := Container.M (Kahn.C α)

#print Kahn.C
#print Kahn.A
#print Kahn.F

#check Container.Obj

def Kahn.corec.automaton {β: Type v} (f: β → F α β) (x: β) : Container.Obj (Kahn.C α) β :=
  match f x with
  | .bot => { fst := Kahn.A.bot, snd := PEmpty.elim}
  | .cons a b => ⟨Kahn.A.cons a, λ _ => b⟩

def Kahn.corec {β: Type v} (f: β → F α β) (x₀: β) : Kahn α :=
  Container.M.corec (corec.automaton f) x₀

def Kahn.dest (k: Kahn α) : Kahn.F α (Kahn α) :=
  match Container.M.destruct k with
  | ⟨.cons x, f⟩ => .cons x (f PUnit.unit)
  | ⟨.bot, _⟩ => .bot

@[simp] theorem Kahn.dest_corec {β: Type v} (f: β → F α β) (x₀: β) :
  dest (corec f x₀) =
    match f x₀ with
    | .cons x xs => .cons x (corec f xs)
    | .bot => .bot := by
  rw [corec]
  simp [corec.automaton, dest, Container.M.destruct_corec]
  match f x₀ with
  | .bot =>
    rfl
  | .cons x xs =>
    rfl


def Kahn.F.mk (k: F α (Kahn α)) : Kahn α :=
  match k with
  | .bot =>
    Container.M.construct ⟨Kahn.A.bot, PEmpty.elim⟩
  | .cons x xs =>
    Container.M.construct ⟨Kahn.A.cons x, λ _ => xs⟩

@[simp] def Kahn.dest_mk (k:F α (Kahn α)) : k.mk.dest = k := by
  match k with
  | .bot =>
    rfl
  | .cons _ xs =>
    rfl

def Kahn.F.mk.inj (k k': F α (Kahn α)) :
  k.mk = k'.mk → k = k' := by
  intro h
  have h := congrArg dest h
  rw [dest_mk, dest_mk] at h
  assumption

@[simp] def Kahn.F.mk.injEq (k k': F α (Kahn α)) :
  (k.mk = k'.mk) = (k = k') := by
  apply propext
  constructor
  . apply inj
  . apply congrArg

instance : Bot (Kahn α) where
  bot := Kahn.F.bot.mk

def Kahn.cons (x: α) (xs: Kahn α) : Kahn α := (F.cons x xs).mk

infixr:67 " ::: " => Kahn.cons

@[app_unexpander Kahn.cons]
def Kahn.unexpandCons : Lean.PrettyPrinter.Unexpander
| `($_ $x $xs) => `($x ::: $xs)
| _ => throw ()

instance : Inhabited (Kahn α) where
  default := ⊥

abbrev Kahn.bot {α} : Kahn α := ⊥

def Kahn.dest_bot : (@bot α).dest = .bot := by rfl

instance : Nonempty (Kahn α) := ⟨default⟩

-- return if a kahn network is a cons
def Kahn.cons? (k: F α β) : Prop :=
  match k with
  | .cons _ _ => True
  | _ => False

instance Kahn.cons?.decide (k: F α β) : Decidable (cons? k) :=
  match k with
  | .cons _ _ => isTrue (by rw [cons?]; trivial)
  | .bot => isFalse (by rw [cons?]; intro h; apply False.elim h)

-- return if a kahn network is an epsilon
def Kahn.bot? (k: F α β) : Prop :=
  match k with
  | .bot => True
  | _ => False

instance Kahn.eps?.decide (k: F α β) : Decidable (bot? k) :=
  match k with
  | .cons _ _ => isFalse (by rw [bot?]; intro h; apply False.elim h)
  | .bot => isTrue (by rw [bot?]; trivial)


@[elab_as_elim, eliminator]
protected def Kahn.cases {motive: Kahn α → Sort w} (x: Kahn α)
  (cons: ∀ a (y: Kahn α), motive (a ::: y))
  (bot: motive ⊥)
  : motive x :=
  Container.M.cases (λ ⟨node, children⟩ =>
    match node with
    | .bot => cast (by simp [Bot.bot, F.mk]; apply congrArg; apply congrArg; simp; funext x; cases x) bot
    | .cons x => cons x (children .unit)
  ) x

@[simp]
protected def Kahn.cases_bot {motive: Kahn α → Sort w}
  (cons: ∀ a (x: Kahn α), motive (a ::: x))
  (bot: motive ⊥) :
  Kahn.cases ⊥ cons bot = bot := by
  rw [Kahn.cases]
  simp [F.mk, Bot.bot]

@[simp]
protected def Kahn.cases_cons {motive: Kahn α → Sort w} (a: α) (x: Kahn α)
  (cons: ∀ a x, motive (a ::: x))
  (bot: motive ⊥) :
  Kahn.cases (a ::: x) cons bot = cons a x := by
  rw [Kahn.cases]
  simp [F.mk, Kahn.cons]

inductive Kahn.eqF (r : Kahn α → Kahn α → Prop) : Kahn α → Kahn α → Prop where
| bot {a b} :
  ⊥ = a → ⊥ = b → eqF r a b
| cons {a b} (x : α) (xs ys: Kahn α) :
  x ::: xs = a → x ::: ys = b → r xs ys → eqF r a b

theorem Kahn.bisim (r : Kahn α → Kahn α → Prop)
  (hyp: ∀ s₁ s₂, r s₁ s₂ → eqF r s₁ s₂) : ∀ x y, r x y → x = y := by
  apply Container.M.bisim
  intro x y h₁
  specialize hyp _ _ h₁
  cases hyp with
  | bot h₁ h₂ =>
    exists (Container.M.destruct x).fst
    exists (Container.M.destruct x).snd
    exists (Container.M.destruct x).snd
    cases h₁
    cases h₂
    simp only [true_and]
    intro e
    apply e.elim
  | cons head xs ys h₁ h₂ h₃ =>
    exists (.cons head)
    exists fun _ => xs
    exists fun _ => ys
    cases h₁
    cases h₂
    constructor
    . rfl
    . constructor
      . rfl
      . intro _
        apply h₃

def Kahn.dest.inj (k k': Kahn α) :
  k.dest = k'.dest → k = k' := by
  intro h
  apply bisim (λ k k' => k.dest = k'.dest) _ _ _ h
  intro s₁ s₂ h₁
  cases s₁ using Kahn.cases with
  | bot =>
    cases s₂ using Kahn.cases with
    | bot =>
      apply eqF.bot <;> rfl
    | cons y ys =>
      simp [Bot.bot, Kahn.cons] at h₁
  | cons x xs =>
    cases s₂ using Kahn.cases with
    | bot =>
      simp [Bot.bot, Kahn.cons] at h₁
    | cons y ys =>
      simp only [Kahn.dest_mk, Kahn.cons, Kahn.F.cons.injEq] at h₁
      induction h₁.left
      induction h₁.right
      apply eqF.cons x xs xs
      . rfl
      . rfl
      . rfl

@[simp] def Kahn.dest.injEq (k k': Kahn α) :
  (k.dest = k'.dest) = (k = k') := by
  apply propext
  constructor
  . apply inj
  . apply congrArg


@[simp] def Kahn.mk_dest (k:Kahn α) : k.dest.mk = k := by
  apply dest.inj
  simp only [dest_mk]

def Kahn.cons.inj (x y: α) (xs ys: Kahn α) :
  x ::: xs = y ::: ys → x = y ∧ xs = ys := by
  intro h
  rw [Kahn.cons, Kahn.cons, F.mk.injEq, F.cons.injEq] at h
  assumption

def Kahn.cons.injEq (x y: α) (xs ys: Kahn α) :
  (x ::: xs = y ::: ys) = (x = y ∧ xs = ys) := by
  apply propext
  constructor
  . apply inj
  . intro h
    induction h.left
    induction h.right
    rfl


theorem Kahn.corec.unfold {β: Type v} (f: β → F α β) (x₀: β) :
  corec f x₀ =
      match f x₀ with
      | .cons x xs => (cons x <| corec f xs)
      | .bot => ⊥ := by
  have := congrArg Kahn.F.mk (dest_corec f x₀)
  rw [mk_dest] at this
  rw [this]
  cases f x₀ with
  | bot =>
    rfl
  | cons x xs =>
    rfl

attribute [eqns Kahn.corec.unfold] Kahn.corec

inductive Kahn.leF (r : Kahn α → Kahn α → Prop) : Kahn α → Kahn α → Prop where
| bot {a b} :
  ⊥ = a→ leF r a b
| cons {a b} (x : α) (xs ys: Kahn α) :
  x ::: xs = a → x ::: ys = b → r xs ys → leF r a b

-- A monotone version of the less than functor
def Kahn.leF.mono : (Kahn α → Kahn α → Prop) →o (Kahn α → Kahn α → Prop) where
  toFun := leF
  monotone' := by
    intro p q h₁ k₁ k₂ h₂
    induction h₂ with
    | cons a xs ys h₂ h₃ h₄ =>
      apply leF.cons a xs ys h₂ h₃
      apply h₁
      assumption
    | bot h₂ =>
      apply leF.bot h₂

instance Kahn.LEinst : LE (Kahn α) where
  le x y := pgfp Kahn.leF.mono ⊥ x y

#check pgfp.accumulate
#check pgfp.coinduction

theorem Kahn.le.coind (α: Type u) (P: Kahn α → Kahn α → Prop)
  (hyp: ∀ x y, P x y → leF (P ⊔ LE.le) x y) :
  ∀ x y, P x y → x ≤ y := by
  intro x y h₁
  simp only [LE.le]
  have h₂ := pgfp.accumulate leF.mono ⊥ P
  apply h₂.2
  . rw [←pgfp.unfold, CompleteLattice.bot_sup]
    have : leF.mono (P ⊔ pgfp leF.mono ⊥) ≤ leF.mono (P ⊔ pgfp leF.mono P) := by
      apply leF.mono.monotone'
      apply sup_le_sup <;> try apply Preorder.le_refl P
      apply (pgfp leF.mono).monotone'
      apply bot_le
    apply Preorder.le_trans _ _ _ _ this
    exact hyp
  . assumption

theorem Kahn.le.unfold {x y: Kahn α} :
  (x ≤ y) = leF (λ x y => x ≤ y) x y := by
  have := pgfp.unfold (@leF.mono α) ⊥
  conv =>
    lhs
    simp only [LE.le]
    rfl
  rw [←this]
  have : ∀ p:((_: Kahn α) × Kahn α → Prop), ⊥ ⊔ p = p := by
    intro p
    funext x
    simp
  simp only [this, CompleteLattice.bot_sup]
  rfl

@[simp] theorem Kahn.leF.mono.def (r: Kahn α → Kahn α → Prop) (x y: Kahn α) :
  leF.mono r x y = leF r x y := by rfl

-- proof of the Scott Continuity of `leF`
instance Kahn.leF.SC : ScottContinuousNat (@Kahn.leF.mono α) where
  scottContinuousNat := by
    intro S x y h₁
    simp only [infᵢ_Prop_eq, infᵢ_apply] at h₁
    induction h₁ 0 with
    | bot h₂ =>
      apply leF.bot h₂
    | cons x xs ys h₂ h₃ _ =>
      induction h₂
      induction h₃
      apply leF.cons x xs ys
      . rfl
      . rfl
      . simp only [infᵢ_apply, infᵢ_Prop_eq]
        intro n
        cases h₁ n with
        | bot h₂ =>
          simp only [Kahn.cons, Bot.bot, F.mk.injEq] at h₂
        | cons a as bs eq₁ eq₂ h =>
          rw [cons.injEq] at eq₁
          rw [cons.injEq] at eq₂
          rw [←eq₁.right, ←eq₂.right]
          assumption

def Kahn.le.refl (x: Kahn α) : x ≤ x := by
  simp only [LE.le]
  coinduction [] generalizing [x] using Kahn.le.coind α; clear x
  intro a b ⟨x, h₁, h₂, h₃⟩; clear h₃
  induction h₁
  induction h₂
  cases x using Kahn.cases with
  | bot =>
    apply leF.bot
    rfl
  | cons x xs =>
    apply leF.cons x xs xs rfl rfl
    apply Or.inl
    exists xs

def Kahn.le.trans (x y z: Kahn α) : x ≤ y → y ≤ z → x ≤ z := by
  intro h₁ h₂
  coinduction [h₁, h₂] generalizing [x, y, z] using Kahn.le.coind α
  clear x y z h₁ h₂
  intro l r ⟨x, y, z, h₁, h₂, h₃, h₄⟩
  induction h₁
  induction h₂
  clear l r
  rw [le.unfold] at h₃ h₄
  cases h₃ with
  | bot h₃ =>
    apply leF.bot h₃
  | cons x xs ys h₁ h₂ h₃ =>
    induction h₁
    induction h₂
    cases h₄ with
    | bot h₄ =>
      simp [Bot.bot, cons] at h₄
    | cons a as bs h₁ h₂ h₄ =>
      induction h₂
      rw [cons.injEq] at h₁
      induction h₁.left
      induction h₁.right
      apply leF.cons a xs bs rfl rfl
      apply Or.inl
      exists xs
      exists as
      exists bs

instance : Preorder (Kahn α) where
  le_refl := Kahn.le.refl
  le_trans := Kahn.le.trans

@[mono]
def Kahn.bot_le (x: Kahn α) : ⊥ ≤ x := by
  rw [le.unfold]
  apply leF.bot rfl

def Kahn.le_bot (x: Kahn α) : x ≤ ⊥ → x = ⊥ := by
  intro h
  rw [le.unfold] at h
  cases h with
  | bot h =>
    exact Eq.symm h
  | cons x xs ys h₁ h₂ h₃ =>
    simp [cons, Bot.bot] at h₂

def Kahn.cons_le (x: α) (xs rhs: Kahn α) :
  (x ::: xs ≤ rhs) → {ys: Kahn α // rhs = x ::: ys ∧ xs ≤ ys} :=
  Kahn.cases rhs
    (cons := λ y ys h =>
      ⟨ys, by
        rw [le.unfold] at h
        cases h with
        | bot h =>
          simp [cons, Bot.bot] at h
        | cons a as bs h₁ h₂ h₃ =>
          rw [cons.injEq] at h₁ h₂
          induction h₁.left
          induction h₂.left
          induction h₁.right
          induction h₂.right
          trivial
      ⟩
    ) (bot := λ h => False.elim (by
      have h' := le_bot (x ::: xs) h
      simp [cons, Bot.bot] at h'
    ))

def Kahn.le_cons (x y: α) (xs ys: Kahn α) :
  x ::: xs ≤ y ::: ys ↔ x = y ∧ xs ≤ ys := by
  constructor
  . intro h₁
    rw [le.unfold] at h₁
    cases h₁ with
    | bot h =>
      simp [Bot.bot, cons] at h
    | cons a as bs h₁ h₂ h₃ =>
      rw [cons.injEq] at h₁ h₂
      induction h₁.right
      induction h₂.right
      induction h₁.left
      induction h₂.left
      trivial
  . intro ⟨h₁, h₂⟩
    induction h₁
    rw [le.unfold]
    apply leF.cons x xs ys rfl rfl h₂

@[mono]
def Kahn.le_of_le_cons (x: α) (xs ys: Kahn α) :
  xs ≤ ys → x ::: xs ≤ x ::: ys := by
  rw [le_cons]
  trivial

inductive Kahn.findCons.Result (f: Nat →o Kahn α) : Type u where
| bot : (∀ n, f n = ⊥) → Result f
| cons (n:ℕ) (x: α) (g: ℕ →o Kahn α) : (∀ k, x ::: g k = f (n+k)) → Result f

def Kahn.findCons.fromIndex {x xs} (f: Nat →o Kahn α) (n:Nat) (h₁: f n = x ::: xs) : Result f :=
  Result.cons n x
    ⟨λ k => (go k).val, by
      intro a b h₁
      have : f (n+a) ≤ f (n+b) := by
        apply f.monotone'
        simp [h₁]
      rw [(go a).property, (go b).property, le_cons] at this
      exact this.2
    ⟩ (fun k =>
      Eq.symm (go k).property
    )
where
  go : ∀ k, {xs: Kahn α // f (n+k) = x ::: xs} := λ k =>
    have h₂ : f n ≤ f (n+k) := by
      apply f.monotone'
      simp
    have ⟨ys, h₃, _⟩ := cons_le x xs (f <| n+k) (by rw [h₁] at h₂; exact h₂)
    ⟨ys, h₃⟩

def Kahn.findCons.exists (f: Nat →o Kahn α) : ∃ _: Result f, True := by
  by_cases (∀ n, f n = ⊥)
  . exists Result.bot h
  . rw [not_forall] at h
    have ⟨n, h⟩ := h
    revert h
    cases h:f n using Kahn.cases with
    | bot => simp [not_true]
    | cons x xs =>
      intro _
      apply Exists.intro (fromIndex f n h) True.intro

noncomputable def Kahn.findCons (f: Nat →o Kahn α) : findCons.Result f :=
  (Classical.indefiniteDescription _ (findCons.exists f)).val


noncomputable def Kahn.lub (f: Nat →o Kahn α) : Kahn α :=
  corec (λ f =>
    match findCons f with
    | .cons _ x xs _ =>
      .cons x xs
    | .bot _ => .bot
  ) f

theorem Kahn.lub.unfold (f: ℕ →o Kahn α) :
  lub f = match findCons f with
          | .cons _ x xs _ => x ::: lub xs
          | .bot _ => ⊥ := by
  rw [lub, corec.unfold]
  cases findCons f with
  | bot _ =>
    rfl
  | cons _ _ _ _ =>
    rfl

theorem Kahn.lub_le (f: ℕ →o Kahn α)(x: Kahn α) (hyp: ∀ n, f n ≤ x) : lub f ≤ x := by
  coinduction [hyp] generalizing [f, x] using le.coind α
  clear hyp f x
  intro a b ⟨f, x, lhs, rhs, hyp⟩
  induction lhs
  induction rhs
  clear a b
  rw [Kahn.lub.unfold]
  cases findCons f with
  | bot h₁ =>
    apply leF.bot rfl
  | cons n y ys h₁ =>
    have h₂ := hyp n
    have h₃ := h₁ 0
    rw [add_zero] at h₃
    rw [←h₃] at h₂
    have ⟨xs, h₄, h₅⟩ := cons_le y (ys 0) x h₂
    induction Eq.symm h₄; clear h₄ x
    apply leF.cons y (lub ys) xs rfl rfl
    apply Or.inl
    exists ys
    exists xs
    constructor
    . rfl
    . constructor
      . rfl
      . intro m
        have : y ::: ys m ≤ y ::: xs := by
          rw [h₁ m]
          apply hyp
        rw [le_cons] at this
        exact this.right


theorem Kahn.le_lub (f: Nat →o Kahn α) (n: Nat) (X : Kahn α) (hX: X ≤ f n) : X ≤ lub f := by
  coinduction [hX] generalizing [X, n, f] using le.coind α
  clear hX X n f
  simp only [and_true]
  intro x y ⟨X, n, f, h₁, h₂, hX⟩
  rw [lub.unfold] at h₁
  induction h₁
  induction h₂
  clear x y
  cases h₁: X with
  | bot =>
    apply leF.bot rfl
  | cons x XS =>
    induction Eq.symm h₁; clear h₁
    have ⟨xs, h₁, _⟩ := cons_le x XS (f n) hX
    cases findCons f with
    | bot h₂ =>
      specialize h₂ n
      simp [h₁, Bot.bot, cons] at h₂
    | cons m a as h₃ =>
      simp only
      have h₄ : x = a := by
        by_cases n ≤ m
        . have h := f.monotone' h
          specialize h₃ 0
          rw [add_zero] at h₃
          rw [h₁, ←h₃, le_cons] at h
          exact h.left
        . rw [not_le] at h
          have h : m+1 ≤ n := h
          have h := f.monotone' h
          specialize h₃ 1
          rw [h₁, ←h₃, le_cons] at h
          exact Eq.symm h.left
      induction h₄
      apply leF.cons x XS (lub as) rfl rfl
      apply Or.inl
      simp
      exists XS
      exists n
      exists as
      constructor
      . rfl
      . constructor
        . rfl
        . apply ((le_cons x x _ _).1 _).2
          rw [h₃ n]
          apply hX.trans
          apply f.monotone'
          simp

noncomputable instance : ωCPO (Kahn α) where
  bot_le {x} := Kahn.bot_le x
  lub := Kahn.lub
  lub_le {f x} h := Kahn.lub_le f x h
  le_lub {f n} := Kahn.le_lub f n (f n) (le_refl _)

#print ωCPO

def Kahn.fst {α: Type u} {β: Type v} (k: Kahn (α × β)) : Kahn α :=
  corec (fun k => Kahn.cases k (cons:= λ  x xs => F.cons x.fst xs) (bot := F.bot)) k

@[simp] theorem Kahn.fst.unfold_bot {α: Type u} {β: Type v} :
  @Kahn.fst α β ⊥ = ⊥ := by
  rw [fst, corec.unfold, Kahn.cases_bot]

@[simp] theorem Kahn.fst.unfold_cons {α: Type u} {β: Type v} (x: α × β) (xs : Kahn (α × β)) :
  @Kahn.fst α β (x ::: xs) = x.fst ::: xs.fst := by
  rw [fst, corec.unfold, Kahn.cases_cons, cons.injEq]
  trivial

attribute [eqns Kahn.fst.unfold_cons Kahn.fst.unfold_bot] Kahn.fst

@[mono]
theorem Kahn.fst.monotone {α: Type u} {β: Type v} :
  ∀ x y: Kahn (α × β), x ≤ y → x.fst ≤ y.fst := by
  intro a b h₁
  coinduction [h₁] generalizing [a, b] using Kahn.le.coind α
  clear h₁ a b
  intro a b ⟨x, y, h₁, h₂, h₃⟩
  induction h₁
  induction h₂
  rw [le.unfold] at h₃
  cases h₃ with
  | bot h₁ =>
    rw [←h₁, fst.unfold_bot]
    apply leF.bot rfl
  | cons x xs ys h₁ h₂ h₃ =>
    rw [←h₁, ←h₂, fst.unfold_cons, fst.unfold_cons]
    apply leF.cons x.fst xs.fst ys.fst rfl rfl
    apply Or.inl
    exists xs
    exists ys


def Kahn.snd {α: Type u} {β: Type v} (k: Kahn (α × β)) : Kahn β :=
  corec (fun k => Kahn.cases k (cons:= λ  x xs => F.cons x.snd xs) (bot := F.bot)) k

@[simp] theorem Kahn.snd.unfold_bot {α: Type u} {β: Type v} :
  @Kahn.snd α β ⊥ = ⊥ := by
  rw [snd, corec.unfold, Kahn.cases_bot]

@[simp] theorem Kahn.snd.unfold_cons {α: Type u} {β: Type v} (x: α × β) (xs : Kahn (α × β)) :
  @Kahn.snd α β (x ::: xs) = x.snd ::: xs.snd := by
  rw [snd, corec.unfold, Kahn.cases_cons, cons.injEq]
  trivial

attribute [eqns Kahn.snd.unfold_cons Kahn.snd.unfold_bot] Kahn.snd

@[mono]
theorem Kahn.snd.monotone {α: Type u} {β: Type v} :
  ∀ x y: Kahn (α × β), x ≤ y → x.snd ≤ y.snd := by
  intro a b h₁
  coinduction [h₁] generalizing [a, b] using Kahn.le.coind β
  clear h₁ a b
  intro a b ⟨x, y, h₁, h₂, h₃⟩
  induction h₁
  induction h₂
  rw [le.unfold] at h₃
  cases h₃ with
  | bot h₁ =>
    rw [←h₁, snd.unfold_bot]
    apply leF.bot rfl
  | cons x xs ys h₁ h₂ h₃ =>
    rw [←h₁, ←h₂, snd.unfold_cons, snd.unfold_cons]
    apply leF.cons x.snd xs.snd ys.snd rfl rfl
    apply Or.inl
    exists xs
    exists ys


def Kahn.tup {α: Type u} {β: Type v} (k₁: Kahn α) (k₂: Kahn β) : Kahn (α × β) :=
  corec (fun (x, y) =>
    match dest x, dest y with
    | .bot, _ => F.bot
    | _, .bot => F.bot
    | .cons x xs, .cons y ys => .cons (x, y) (xs, ys)
  ) (k₁, k₂)

@[simp] theorem Kahn.tup.unfold_bot_left {α: Type u} {β: Type v} (k₂: Kahn β) :
  @tup α β ⊥ k₂ = ⊥ := by
  rw [tup, corec.unfold]
  simp [dest_bot]

@[simp] theorem Kahn.tup.unfold_bot_right {α: Type u} {β: Type v} (k₁: Kahn α) :
  @tup α β k₁ ⊥ = ⊥ := by
  rw [tup, corec.unfold]
  simp [dest_bot]
  cases dest k₁ <;> rfl

@[simp] theorem Kahn.tup.unfold_cons {α: Type u} {β: Type v} (x: α) (xs: Kahn α) (y: β) (ys: Kahn β) :
  @tup α β (x ::: xs) (y ::: ys) = (x, y) ::: tup xs ys := by
  rw [tup, corec.unfold]
  have h₁ : dest (x ::: xs) = .cons x xs := by rfl
  have h₂ : dest (y ::: ys) = .cons y ys := by rfl
  simp only [h₁, h₂]
  rfl

attribute [eqns Kahn.tup.unfold_cons Kahn.tup.unfold_bot_left Kahn.tup.unfold_bot_right] Kahn.tup

@[simp] theorem Kahn.tup_fst_snd {α: Type u} {β: Type v} (k: Kahn (α × β)) :
  tup k.fst k.snd = k := by
  coinduction [] generalizing [k] using bisim
  clear k
  intro s₁ s₂ ⟨x, h₁, h₂, _⟩
  induction h₁
  cases x with
  | bot =>
    simp only [fst.unfold_bot, tup.unfold_bot_left] at h₂
    induction h₂
    apply eqF.bot rfl rfl
  | cons x xs =>
    --rw [fst] at h₂
    simp only [fst.unfold_cons, snd.unfold_cons, tup.unfold_cons, Prod.mk.eta] at h₂
    induction h₂
    apply eqF.cons x (tup xs.fst xs.snd) xs rfl rfl
    exists xs

@[mono] theorem Kahn.tup.monotone {α: Type u} {β: Type v} :
  ∀ (x y: Kahn α) (z w: Kahn β), x ≤ y → z ≤ w → tup x z ≤ tup y w := by
  intro x y z w h₁ h₂
  coinduction [h₁, h₂] generalizing [x, y, z, w] using Kahn.le.coind _
  clear h₁ h₂ x y z w
  intro X Y ⟨x, y, z, w, h₁, h₂, h₃, h₄⟩
  induction h₁
  induction h₂
  rw [le.unfold] at h₃ h₄
  cases h₃ with
  | bot h =>
    induction h
    simp [unfold_bot_left]
    apply leF.bot rfl
  | cons x xs ys h₁ h₂ h₃ =>
    induction h₁
    induction h₂
    cases h₄ with
    | bot h =>
      induction h
      simp [unfold_bot_right]
      apply leF.bot rfl
    | cons z zs ws h₁ h₂ h₄ =>
      induction h₁
      induction h₂
      rw [unfold_cons, unfold_cons]
      apply leF.cons (x, z) (tup xs zs) (tup ys ws) rfl rfl
      apply Or.inl
      exists xs
      exists ys
      exists zs
      exists ws

def Kahn.fby (x y: Kahn α) : Kahn α :=
  Kahn.cases x (cons := λ x _ => x ::: y) (bot := ⊥)

def Kahn.fby.unfold_bot (x: Kahn α) : fby ⊥ x = ⊥ := by
  rw [fby, Kahn.cases_bot]

def Kahn.fby.unfold_cons (x : α) (xs y: Kahn α) :
  fby (x ::: xs) y = x ::: y := by
  rw [fby, Kahn.cases_cons]

attribute [eqns Kahn.fby.unfold_bot Kahn.fby.unfold_cons] Kahn.fby

@[mono]
theorem Kahn.fby.monotone (x y z w: Kahn α) :
  x ≤ y → z ≤ w → fby x z ≤ fby y w := by
  intro h₁ h₂
  rw [le.unfold] at h₁
  cases h₁ with
  | bot h =>
    induction h
    rw [unfold_bot]
    apply bot_le
  | cons x xs ys h₁ h₂ h₃ =>
    induction h₁
    induction h₂
    rw [unfold_cons, unfold_cons, le_cons]
    trivial

