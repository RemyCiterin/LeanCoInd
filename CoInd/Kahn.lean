import CoInd.M
import CoInd.Paco
import CoInd.Tactic
import CoInd.Container
import CoInd.Utils
import Mathlib.Tactic.Eqns
import CoInd.Std.DelabRule
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.OmegaCompletePartialOrder
import CoInd.OmegaCompletePartialOrder
import CoInd.Notation

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Monotonicity.Basic

import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq

#print OmegaCompletePartialOrder


open OmegaCompletePartialOrder

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
  · apply inj
  · apply congrArg

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


@[elab_as_elim, cases_eliminator]
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
    · rfl
    · constructor
      · rfl
      · intro _
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
      · rfl
      · rfl
      · rfl

@[simp] def Kahn.dest.injEq (k k': Kahn α) :
  (k.dest = k'.dest) = (k = k') := by
  apply propext
  constructor
  · apply inj
  · apply congrArg


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
  · apply inj
  · intro h
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

--attribute [eqns Kahn.corec.unfold] Kahn.corec

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
  · rw [←pgfp.unfold, CompleteLattice.bot_sup]
    have : leF.mono (P ⊔ pgfp leF.mono ⊥) ≤ leF.mono (P ⊔ pgfp leF.mono P) := by
      apply leF.mono.monotone'
      apply sup_le_sup <;> try apply Preorder.le_refl P
      apply (pgfp leF.mono).monotone'
      apply bot_le
    apply Preorder.le_trans _ _ _ _ this
    exact hyp
  · assumption

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
    simp only [iInf_Prop_eq, iInf_apply] at h₁
    induction h₁ 0 with
    | bot h₂ =>
      apply leF.bot h₂
    | cons x xs ys h₂ h₃ _ =>
      induction h₂
      induction h₃
      apply leF.cons x xs ys
      · rfl
      · rfl
      · simp only [iInf_apply, iInf_Prop_eq]
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
  coinduction generalizing [x] using Kahn.le.coind α; clear x
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
  coinduction generalizing [x, y, z] using Kahn.le.coind α
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
  · intro h₁
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
  · intro ⟨h₁, h₂⟩
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
| cons (n:ℕ) (x: α) (g: Chain (Kahn α)) : (∀ k, x ::: g k = f (n+k)) → Result f

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
  by_cases h:(∀ n, f n = ⊥)
  · exists Result.bot h
  · rw [not_forall] at h
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
  coinduction generalizing [f, x] using le.coind α
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
    let ⟨xs, h₄, _⟩ := cons_le y (ys 0) x h₂
    induction Eq.symm h₄; clear h₄ x
    apply leF.cons y (lub ys) xs rfl rfl
    apply Or.inl
    exists ys
    exists xs
    constructor
    · rfl
    · constructor
      · rfl
      · intro m
        have : y ::: ys m ≤ y ::: xs := by
          rw [h₁ m]
          apply hyp
        rw [le_cons] at this
        exact this.right


theorem Kahn.le_lub (f: Nat →o Kahn α) (n: Nat) (X : Kahn α) (hX: X ≤ f n) : X ≤ lub f := by
  coinduction generalizing [X, n, f] using le.coind α
  clear hX X n f
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
        by_cases h:n ≤ m
        · have h := f.monotone h
          specialize h₃ 0
          rw [add_zero] at h₃
          rw [h₁, ←h₃, le_cons] at h
          exact h.left
        · rw [not_le] at h
          have h : m+1 ≤ n := h
          have h := f.monotone h
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
      · rfl
      · constructor
        · rfl
        · apply ((le_cons x x _ _).1 _).2
          rw [h₃ n]
          apply hX.trans
          apply f.monotone'
          simp

noncomputable instance : OmegaCompletePartialOrder (Kahn α) where
  le_antisymm := by
    intro a b h₁ h₂
    coinduction generalizing [a, b] using Kahn.bisim
    clear h₁ h₂ a b
    intro s₁ s₂ ⟨a, b, eq₁, eq₂, h₁, h₂⟩
    induction eq₁
    induction eq₂
    rw [Kahn.le.unfold] at h₁
    cases h₁ with
    | bot h₁ =>
      induction h₁
      have := Kahn.le_bot _ h₂
      induction Eq.symm this
      induction h₂
      apply Kahn.eqF.bot rfl rfl
    | cons x xs ys eq₁ eq₂ h₁ =>
      induction eq₁
      induction eq₂
      rw [Kahn.le_cons] at h₂
      have h₃ := h₂.right
      apply Kahn.eqF.cons x xs ys rfl rfl
      exists xs
      exists ys

  ωSup := Kahn.lub

  ωSup_le f x h := Kahn.lub_le f x h
  le_ωSup f n := Kahn.le_lub f n (f n) (le_refl _)

theorem Kahn.ωSup.unfold (f: ℕ →o Kahn α) :
  ωSup f = match findCons f with
          | .cons _ x xs _ => x ::: ωSup xs
          | .bot _ => ⊥ :=
  lub.unfold f

theorem Kahn.ωSup_bot (f: ℕ →o Kahn α) :
  (∀ n, f n = ⊥) → ωSup f = ⊥ := by
  intro h
  rw [ωSup.unfold]
  cases findCons f with
  | bot _ =>
    trivial
  | cons n x xs h' =>
    specialize h n
    specialize h' 0
    rw [Nat.add_zero] at h'
    exfalso
    rw [h] at h'
    simp [cons, Bot.bot] at h'

#print Kahn.findCons.Result

theorem Kahn.ωSup_cons (f: ℕ →o Kahn α) :
  (n : ℕ) → (x : α) → (xs : ℕ →o Kahn α) → (∀ (k : ℕ), x ::: xs k = f (n + k)) →
  ωSup f = x ::: ωSup xs :=  by
  intro n x xs h₁
  rw [Kahn.ωSup.unfold f]
  cases findCons f with
  | bot h₂ =>
    specialize h₁ 0
    specialize h₂ n
    rw [Nat.add_zero, h₂] at h₁
    simp [cons, Bot.bot] at h₁
  | cons m y ys h₂ =>
    have h₃ := h₁ m
    have h₄ := h₂ n
    rw [Nat.add_comm, ←h₄, cons.injEq] at h₃
    induction h₃.left
    simp only [cons.injEq, true_and]
    apply le_antisymm
    <;> apply ωSup_le
    <;> intro k
    · calc
        ys k ≤ ys (n + k) := ys.monotone (by simp_arith)
        _ ≤ xs (m + k) := by
          specialize h₁ (m+k)
          specialize h₂ (n+k)
          have : n + (m + k) = m + (n + k) := by simp_arith
          rw [this, ←h₂, cons.injEq] at h₁
          rw [h₁.right]
        _ ≤ ωSup xs := le_ωSup _ _
    · calc
        xs k ≤ xs (m + k) := xs.monotone (by simp_arith)
        _ ≤ ys (n + k) := by
          specialize h₁ (m+k)
          specialize h₂ (n+k)
          have : n + (m + k) = m + (n + k) := by simp_arith
          rw [this, ←h₂, cons.injEq] at h₁
          rw [h₁.right]
        _ ≤ ωSup ys := le_ωSup _ _

def OmegaCompletePartialOrder.Chain.offset [OmegaCompletePartialOrder α] (f: Chain α) (n: ℕ) : Chain α where
    toFun k := f (n+k)
    monotone' x y h₁ := f.monotone (by simp_arith [h₁])

def OmegaCompletePartialOrder.Chain.ωSup_offset [OmegaCompletePartialOrder α] (f: Chain α) (n: ℕ) :
  ωSup (f.offset n) = ωSup f := by
  apply le_antisymm
  <;> apply ωSup_le
  <;> intro m
  · apply le_ωSup f (n+m)
  · calc
      f m ≤ f (n + m) := f.monotone (by simp_arith)
      _ ≤ f.offset n m := le_refl _
      _ ≤ _ := le_ωSup _ _



def Kahn.findCons.Result.offset (m: ℕ) (f: ℕ →o Kahn α)
  (n : ℕ) (x : α) (xs : Chain (Kahn α)) (hyp: ∀ (k : ℕ), x ::: xs k = f (n + k)) :
  {ys: Chain (Kahn α) // ∀ k, x ::: ys k = f ((n + m) + k)} where
  val := xs.offset m
  property k := by
    rw [OmegaCompletePartialOrder.Chain.offset, OrderHom.mk_apply, hyp]
    apply congrArg f
    simp_arith

#check Kahn.corec
#print Kahn.F
def Kahn.fst {α: Type u} {β: Type v} (k: Kahn (α × β)) : Kahn α :=
  corec (fun k => Kahn.cases k (cons:= λ x xs => F.cons x.fst xs) (bot := F.bot)) k

@[simp] theorem Kahn.fst.unfold_bot {α: Type u} {β: Type v} :
  @Kahn.fst α β ⊥ = ⊥ := by
  rw [fst, corec.unfold, Kahn.cases_bot]

@[simp] theorem Kahn.fst.unfold_cons {α: Type u} {β: Type v} (x: α × β) (xs : Kahn (α × β)) :
  @Kahn.fst α β (x ::: xs) = x.fst ::: xs.fst := by
  rw [fst, corec.unfold, Kahn.cases_cons, cons.injEq]
  trivial

--attribute [eqns Kahn.fst.unfold_cons Kahn.fst.unfold_bot] Kahn.fst

@[mono]
theorem Kahn.fst.monotone {α: Type u} {β: Type v} :
  ∀ x y: Kahn (α × β), x ≤ y → x.fst ≤ y.fst := by
  intro a b h₁
  coinduction generalizing [a, b] using Kahn.le.coind α
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

@[simps! coe]
def OrderHom.Kahn.fst {α: Type u} {β: Type v} : Kahn (α × β) →o Kahn α where
  toFun := _root_.Kahn.fst
  monotone' {x y} h := Kahn.fst.monotone x y h

#check Kahn.ωSup_bot
#check Kahn.ωSup_cons

theorem Kahn.fst.continuous {α: Type u} {β: Type v} :
  OmegaCompletePartialOrder.Continuous (@OrderHom.Kahn.fst α β) := by
  intro chain
  unfold OrderHom.Kahn.fst
  coinduction generalizing [chain] using Kahn.bisim
  clear chain
  rintro s₁ s₂ ⟨chain, h₁, h₂, _⟩
  induction h₁
  induction h₂
  clear s₁ s₂
  cases findCons chain with
  | bot h =>
    apply eqF.bot
    · rw [ωSup_bot]
      · simp only [OrderHom.mk_apply, unfold_bot]
      · assumption
    · rw [ωSup_bot]
      intro n
      specialize h n
      simp only [Chain.map, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, h, unfold_bot]
  | cons n x xs h =>
    apply eqF.cons x.fst (ωSup xs).fst (ωSup (OrderHom.comp ⟨fst, fst.monotone⟩ xs))
    · rw [ωSup_cons chain n x xs, OrderHom.mk_apply, fst.unfold_cons]
      assumption
    · conv =>
        rhs
        rw [ωSup_cons _ n x.fst (OrderHom.comp ⟨fst, fst.monotone⟩ xs)]
        rfl
        tactic =>
          intro m
          simp only [OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, Chain.map]
          rw [←h m]
          simp [unfold_cons]
    · exists xs

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.Kahn.fst {α: Type u} {β: Type v} : Kahn (α × β) →𝒄 Kahn α where
  toFun := _root_.Kahn.fst
  monotone' := OrderHom.Kahn.fst.monotone
  cont := Kahn.fst.continuous

def Kahn.snd {α: Type u} {β: Type v} (k: Kahn (α × β)) : Kahn β :=
  corec (fun k => Kahn.cases k (cons:= λ  x xs => F.cons x.snd xs) (bot := F.bot)) k

@[simp] theorem Kahn.snd.unfold_bot {α: Type u} {β: Type v} :
  @Kahn.snd α β ⊥ = ⊥ := by
  rw [snd, corec.unfold, Kahn.cases_bot]

@[simp] theorem Kahn.snd.unfold_cons {α: Type u} {β: Type v} (x: α × β) (xs : Kahn (α × β)) :
  @Kahn.snd α β (x ::: xs) = x.snd ::: xs.snd := by
  rw [snd, corec.unfold, Kahn.cases_cons, cons.injEq]
  trivial

--attribute [eqns Kahn.snd.unfold_cons Kahn.snd.unfold_bot] Kahn.snd

@[mono]
theorem Kahn.snd.monotone {α: Type u} {β: Type v} :
  ∀ x y: Kahn (α × β), x ≤ y → x.snd ≤ y.snd := by
  intro a b h₁
  coinduction generalizing [a, b] using Kahn.le.coind β
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

@[simps! coe]
def OrderHom.Kahn.snd {α: Type u} {β: Type v} : Kahn (α × β) →o Kahn β where
  toFun := _root_.Kahn.snd
  monotone' {x y} h := Kahn.snd.monotone x y h

theorem Kahn.snd.continuous {α: Type u} {β: Type v} :
  OmegaCompletePartialOrder.Continuous (@OrderHom.Kahn.snd α β) := by
  unfold OrderHom.Kahn.snd
  intro chain
  coinduction generalizing [chain] using Kahn.bisim
  clear chain
  rintro s₁ s₂ ⟨chain, h₁, h₂, _⟩
  induction h₁
  induction h₂
  clear s₁ s₂
  cases findCons chain with
  | bot h =>
    apply eqF.bot
    · rw [ωSup_bot]
      · simp only [OrderHom.mk_apply, unfold_bot]
      · assumption
    · rw [ωSup_bot]
      intro n
      specialize h n
      simp only [Chain.map, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, h, unfold_bot]
  | cons n x xs h =>
    apply eqF.cons x.snd (ωSup xs).snd (ωSup (OrderHom.comp ⟨snd, snd.monotone⟩ xs))
    · rw [ωSup_cons chain n x xs, OrderHom.mk_apply, snd.unfold_cons]
      assumption
    · conv =>
        rhs
        rw [ωSup_cons _ n x.snd (OrderHom.comp ⟨snd, snd.monotone⟩ xs)]
        rfl
        tactic =>
          intro m
          simp only [OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, Chain.map]
          rw [←h m]
          simp [unfold_cons]
    · exists xs

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.Kahn.snd {α: Type u} {β: Type u} : Kahn (α × β) →𝒄 Kahn β where
  toFun := _root_.Kahn.snd
  monotone' := Kahn.snd.monotone
  cont := Kahn.snd.continuous


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

--attribute [eqns Kahn.tup.unfold_cons Kahn.tup.unfold_bot_left Kahn.tup.unfold_bot_right] Kahn.tup

@[simp] theorem Kahn.tup_fst_snd {α: Type u} {β: Type v} (k: Kahn (α × β)) :
  tup k.fst k.snd = k := by
  coinduction generalizing [k] using bisim
  clear k
  intro s₁ s₂ ⟨x, h₁, h₂, _⟩
  induction h₁
  cases x with
  | bot =>
    simp only [fst.unfold_bot, tup.unfold_bot_left] at h₂
    induction h₂
    apply eqF.bot rfl rfl
  | cons x xs =>
    simp only [fst.unfold_cons, snd.unfold_cons, tup.unfold_cons, Prod.mk.eta] at h₂
    induction h₂
    apply eqF.cons x (tup xs.fst xs.snd) xs rfl rfl
    exists xs

@[mono] theorem Kahn.tup.monotone {α: Type u} {β: Type v} :
  ∀ (x y: Kahn α) (z w: Kahn β), x ≤ y → z ≤ w → tup x z ≤ tup y w := by
  intro x y z w h₁ h₂
  coinduction generalizing [x, y, z, w] using Kahn.le.coind _
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

@[simps! coe]
def OrderHom.Kahn.tup {α: Type u} {β: Type v} : Kahn α →o Kahn β →o Kahn (α × β) :=
  OrderHom.curry
    { toFun := λ (x, y) => _root_.Kahn.tup x y
    , monotone' := λ _ _ h => Kahn.tup.monotone _ _ _ _ h.left h.right}

def Kahn.tup.continuous {α : Type u} {β: Type v} :
  OmegaCompletePartialOrder.Continuous (OrderHom.curry.symm (@OrderHom.Kahn.tup α β)) := by
  intro chain
  simp only [OrderIso.symm, OrderHom.curry, OrderHom.Kahn.tup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
    OrderHom.coe_mk, RelIso.coe_fn_symm_mk, Equiv.coe_fn_symm_mk, OrderHom.mk_apply, Function.uncurry_curry,
    Prod.instOmegaCompletePartialOrder_ωSup_fst, Prod.instOmegaCompletePartialOrder_ωSup_snd]
  have ⟨(lhs, rhs), h₁⟩ : {p: Chain (Kahn α) × Chain (Kahn β) // p.fst.zip p.snd = chain} :=
    ⟨(chain.map OrderHom.fst, chain.map OrderHom.snd), by
      apply OrderHom.ext
      funext n
      rfl
    ⟩
  induction h₁
  have h₁ : (lhs.zip rhs).map OrderHom.fst = lhs := rfl
  have h₂ : (lhs.zip rhs).map OrderHom.snd = rhs := rfl
  simp only [h₁, h₂]
  clear h₁ h₂
  coinduction generalizing [lhs, rhs] using Kahn.bisim
  let monoTup : Kahn α × Kahn β →o Kahn (α × β) :=
    ⟨λ p => p.1.tup p.2, λ (x, y) (z, t) h => tup.monotone x z y t h.left h.right⟩
  intro s₁ s₂ ⟨lhs, rhs, eq₁, eq₂, _⟩
  induction eq₁
  induction eq₂
  cases findCons lhs with
  | bot h₁ =>
    apply eqF.bot
    rw [ωSup_bot lhs]
    · rw [Kahn.tup.unfold_bot_left]
    · assumption
    · rw [ωSup_bot]
      intro n
      simp only
        [Chain.map, Chain.zip, OrderHom.comp_coe, OrderHom.coe_mk,
        Function.comp_apply, OrderHom.prod_coe, h₁ n, tup.unfold_bot_left]
  | cons n x xs h₁ =>
    cases findCons rhs with
    | bot h₂ =>
      apply eqF.bot
      rw [ωSup_bot rhs]
      · rw [Kahn.tup.unfold_bot_right]
      · assumption
      · rw [ωSup_bot]
        intro n
        simp only
          [Chain.map, Chain.zip, OrderHom.comp_coe, OrderHom.coe_mk,
          Function.comp_apply, OrderHom.prod_coe, h₂ n, tup.unfold_bot_right]
    | cons m y ys h₂ =>
      have ⟨ys, h₂⟩ := findCons.Result.offset n _ _ y ys h₂
      have ⟨xs, h₁⟩ := findCons.Result.offset m _ _ x xs h₁
      rw [Nat.add_comm m n] at h₂
      apply eqF.cons (x, y)
        ((ωSup xs).tup (ωSup ys))
        (ωSup ((xs.zip ys).map monoTup))
      · rw [ωSup_cons lhs (n+m) x xs, ωSup_cons rhs (n+m) y ys]
        · simp only [tup.unfold_cons]
        · assumption
        · assumption
      · rw [ωSup_cons ((lhs.zip rhs).map monoTup) (n+m) (x, y) ((xs.zip ys).map monoTup)]
        · intro k
          specialize h₁ k
          specialize h₂ k
          simp only [Chain.map, Chain.zip, OrderHom.comp_coe,
            OrderHom.coe_mk, Function.comp_apply, OrderHom.prod_coe, ←
            h₁, ← h₂, tup.unfold_cons, monoTup]
      · exists xs
        exists ys

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.Kahn.tup {α: Type u} {β: Type v} :
  Kahn α →𝒄 Kahn β →𝒄 Kahn (α × β) :=
  OmegaCompletePartialOrder.ContinuousHom.Prod.curry {
    toFun := λ (x, y) => _root_.Kahn.tup x y,
    monotone' := λ _ _ ⟨h₁, h₂⟩ => Kahn.tup.monotone _ _ _ _ h₁ h₂,
    cont := Kahn.tup.continuous
  }

#check Kahn.ωSup_cons

def Kahn.fby (x y: Kahn α) : Kahn α :=
  Kahn.cases x (cons := λ x _ => x ::: y) (bot := ⊥)

@[simp] def Kahn.fby.unfold_bot (x: Kahn α) : fby ⊥ x = ⊥ := by
  rw [fby, Kahn.cases_bot]

@[simp] def Kahn.fby.unfold_cons (x : α) (xs y: Kahn α) :
  fby (x ::: xs) y = x ::: y := by
  rw [fby, Kahn.cases_cons]

--attribute [eqns Kahn.fby.unfold_bot Kahn.fby.unfold_cons] Kahn.fby

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

@[simps! coe]
def OrderHom.Kahn.fby : Kahn α →o Kahn α →o Kahn α :=
  OrderHom.curry {toFun := λ (x, y) => _root_.Kahn.fby x y, monotone' := λ  _ _ ⟨h₁, h₂⟩ => Kahn.fby.monotone _ _ _ _ h₁ h₂}


def Kahn.fby.continuous :
  OmegaCompletePartialOrder.Continuous (OrderHom.curry.symm (@OrderHom.Kahn.fby α)) := by
  intro chain
  simp only [OrderHom.Kahn.fby, OrderIso.symm_apply_apply, OrderHom.mk_apply,
    Prod.instOmegaCompletePartialOrder_ωSup_fst, Prod.instOmegaCompletePartialOrder_ωSup_snd]
  let ⟨(lhs, rhs), h₁⟩ : {p: Chain (Kahn α) × Chain (Kahn α) // p.fst.zip p.snd = chain} :=
    ⟨(chain.map OrderHom.fst, chain.map OrderHom.snd), by
      apply OrderHom.ext
      funext n
      rfl
    ⟩
  induction h₁
  have h₁ : (lhs.zip rhs).map OrderHom.fst = lhs := rfl
  have h₂ : (lhs.zip rhs).map OrderHom.snd = rhs := rfl
  simp only [h₁, h₂]
  clear h₁ h₂
  cases findCons lhs with
  | bot h₁ =>
    rw [ωSup_bot lhs, fby.unfold_bot]
    · rw [ωSup_bot]
      intro n
      simp only [Chain.map, Chain.zip, OrderHom.comp_coe,
        OrderHom.coe_mk, Function.comp_apply, OrderHom.prod_coe,
        h₁ n, fby.unfold_bot]
    · assumption
  | cons n x xs h₁ =>
    rw [ωSup_cons lhs n x xs h₁, fby.unfold_cons]
    rw [ωSup_cons ((lhs.zip rhs).map _) n x (rhs.offset n)]
    · rw [OmegaCompletePartialOrder.Chain.ωSup_offset]
    · intro k
      simp only [Chain.map, Chain.zip, OrderHom.comp_coe,
        OrderHom.coe_mk, Function.comp_apply, OrderHom.prod_coe, ←
        h₁ k, fby.unfold_cons]
      rfl

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.Kahn.fby : Kahn α →𝒄 Kahn α →𝒄 Kahn α :=
  OmegaCompletePartialOrder.ContinuousHom.Prod.curry
    { toFun := λ (x, y) => _root_.Kahn.fby x y
    , monotone' := λ _ _ ⟨h₁, h₂⟩ => Kahn.fby.monotone _ _ _ _ h₁ h₂
    , cont := Kahn.fby.continuous}

def Kahn.map {α: Type u} {β: Type v} (f: α → β) (x: Kahn α) : Kahn β :=
  Kahn.corec (λ x =>
      Kahn.cases x (cons := λ x xs =>
        .cons (f x) xs
      ) (bot := .bot)
    ) x

@[simp] def Kahn.map.unfold_bot {α: Type u} {β: Type v} (f: α → β) :
  map f ⊥ = ⊥ := by
  rw [map, corec.unfold, Kahn.cases_bot]

@[simp] def Kahn.map.unfold_cons {α: Type u} {β: Type v} (f: α → β) (x: α) (xs: Kahn α) :
  map f (x ::: xs) = f x ::: map f xs := by
  rw [map, corec.unfold, Kahn.cases_cons]
  rfl

--attribute [eqns Kahn.map.unfold_bot Kahn.map.unfold_cons] Kahn.map

@[mono] theorem Kahn.map.monotone {α: Type u} {β: Type v} (f: α → β) :
  ∀ x y, x ≤ y → map f x ≤ map f y := by
  intro x y h₁
  coinduction generalizing [x, y] using Kahn.le.coind _
  clear h₁ x y
  intro _ _ ⟨x, y, h₁, h₂, h₃⟩
  induction h₁
  induction h₂
  rw [le.unfold] at h₃
  cases h₃ with
  | bot h =>
    induction h
    rw [map.unfold_bot]
    apply leF.bot rfl
  | cons x xs ys h₁ h₂ h₃ =>
    induction h₁
    induction h₂
    rw [unfold_cons, unfold_cons]
    apply leF.cons (f x) (map f xs) (map f ys) rfl rfl
    apply Or.inl
    exists xs
    exists ys

@[simps! coe]
def OrderHom.Kahn.map {α: Type u} {β: Type v} (f: α → β) : Kahn α →o Kahn β where
  toFun := _root_.Kahn.map f
  monotone' := Kahn.map.monotone f

def Kahn.map.continuous {α: Type u} {β: Type v} (f: α → β) :
  OmegaCompletePartialOrder.Continuous (OrderHom.Kahn.map f) := by
  intro chain
  unfold OrderHom.Kahn.map
  coinduction generalizing [chain] using Kahn.bisim
  clear chain
  intro s₁ s₂ ⟨chain, eq₁, eq₂, h⟩
  clear h
  induction eq₁
  induction eq₂
  cases findCons chain with
  | bot h₁ =>
    apply eqF.bot
    · rw [ωSup_bot, OrderHom.mk_apply, map.unfold_bot]
      assumption
    · rw [ωSup_bot]
      intro n
      simp [Chain.map, h₁ n]
  | cons n x xs h₁ =>
    apply eqF.cons (f x) (map f (ωSup xs)) (ωSup (xs.map ⟨Kahn.map f, Kahn.map.monotone f⟩))
    · rw [OrderHom.mk_apply, ωSup_cons chain n x xs]
      · rw [map.unfold_cons]
      · assumption
    · rw [ωSup_cons (chain.map _) n (f x) (xs.map ⟨map f, map.monotone f⟩)]
      simp only [Chain.map, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply]
      intro k
      rw [←h₁ k, map.unfold_cons]
    · exists xs

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.Kahn.map {α: Type u} {β: Type v} (f: α → β) : Kahn α →𝒄 Kahn β where
  toFun := _root_.Kahn.map f
  monotone' := Kahn.map.monotone f
  cont := Kahn.map.continuous f

