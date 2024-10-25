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

inductive ωStream.A (α: Type u) where
| cons : α → ωStream.A α
| bot

def ωStream.B {α: Type u} : ωStream.A α → Type u
| .cons _ => PUnit
| _ => PEmpty

def ωStream.C (α: Type u) : Container := ⟨A α, ωStream.B⟩

inductive ωStream.F (α: Type u) (β: Type v) where
| cons : α → β → F α β
| bot : F α β

instance [Inhabited β] : Inhabited (ωStream.F α β) where
  default := .bot

def ωStream (α: Type u) : Type u := Container.M (ωStream.C α)

#print ωStream.C
#print ωStream.A
#print ωStream.F

#check Container.Obj

def ωStream.corec.automaton
  {β: Type v} (f: β → F α β) (x: β) : Container.Obj (ωStream.C α) β :=
  match f x with
  | .bot => { fst := ωStream.A.bot, snd := PEmpty.elim}
  | .cons a b => ⟨ωStream.A.cons a, λ _ => b⟩

def ωStream.corec {β: Type v} (f: β → F α β) (x₀: β) : ωStream α :=
  Container.M.corec (corec.automaton f) x₀

def ωStream.dest (k: ωStream α) : ωStream.F α (ωStream α) :=
  match Container.M.destruct k with
  | ⟨.cons x, f⟩ => .cons x (f PUnit.unit)
  | ⟨.bot, _⟩ => .bot

@[simp] theorem ωStream.dest_corec {β: Type v} (f: β → F α β) (x₀: β) :
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


def ωStream.F.mk (k: F α (ωStream α)) : ωStream α :=
  match k with
  | .bot =>
    Container.M.construct ⟨ωStream.A.bot, PEmpty.elim⟩
  | .cons x xs =>
    Container.M.construct ⟨ωStream.A.cons x, λ _ => xs⟩

@[simp] def ωStream.dest_mk (k:F α (ωStream α)) : k.mk.dest = k := by
  match k with
  | .bot =>
    rfl
  | .cons _ xs =>
    rfl

def ωStream.F.mk.inj (k k': F α (ωStream α)) :
  k.mk = k'.mk → k = k' := by
  intro h
  have h := congrArg dest h
  rw [dest_mk, dest_mk] at h
  assumption

@[simp] def ωStream.F.mk.injEq (k k': F α (ωStream α)) :
  (k.mk = k'.mk) = (k = k') := by
  apply propext
  constructor
  · apply inj
  · apply congrArg

instance : Bot (ωStream α) where
  bot := ωStream.F.bot.mk

class Cons (α: outParam (Sort u)) (β: Sort v) where
  cons: α → β → β

infixr:67 " ::: " => Cons.cons

instance : Cons α (ωStream α) where
  cons x xs := (ωStream.F.cons x xs).mk


@[app_unexpander Cons.cons]
def ωStream.unexpandCons : Lean.PrettyPrinter.Unexpander
| `($_ $x $xs) => `($x ::: $xs)
| _ => throw ()

instance : Inhabited (ωStream α) where
  default := ⊥

abbrev ωStream.bot {α} : ωStream α := ⊥

def ωStream.dest_bot : (@bot α).dest = .bot := by rfl

instance : Nonempty (ωStream α) := ⟨default⟩

-- return if a kahn network is a cons
def ωStream.cons? (k: F α β) : Prop :=
  match k with
  | .cons _ _ => True
  | _ => False

instance ωStream.cons?.decide (k: F α β) : Decidable (cons? k) :=
  match k with
  | .cons _ _ => isTrue (by rw [cons?]; trivial)
  | .bot => isFalse (by rw [cons?]; intro h; apply False.elim h)

-- return if a kahn network is an epsilon
def ωStream.bot? (k: F α β) : Prop :=
  match k with
  | .bot => True
  | _ => False

instance ωStream.eps?.decide (k: F α β) : Decidable (bot? k) :=
  match k with
  | .cons _ _ => isFalse (by rw [bot?]; intro h; apply False.elim h)
  | .bot => isTrue (by rw [bot?]; trivial)


@[elab_as_elim, cases_eliminator]
protected def ωStream.cases {motive: ωStream α → Sort w} (x: ωStream α)
  (cons: ∀ a (y: ωStream α), motive (a ::: y))
  (bot: motive ⊥)
  : motive x :=
  Container.M.cases (λ ⟨node, children⟩ =>
    match node with
    | .bot => cast
      (by simp [Bot.bot, F.mk]
          apply congrArg
          apply congrArg
          simp
          funext x
          cases x
      ) bot
    | .cons x => cons x (children .unit)
  ) x

@[simp]
protected def ωStream.cases_bot {motive: ωStream α → Sort w}
  (cons: ∀ a (x: ωStream α), motive (a ::: x))
  (bot: motive ⊥) :
  ωStream.cases ⊥ cons bot = bot := by
  rw [ωStream.cases]
  simp [F.mk, Bot.bot]

@[simp]
protected def ωStream.cases_cons {motive: ωStream α → Sort w} (a: α) (x: ωStream α)
  (cons: ∀ a x, motive (a ::: x))
  (bot: motive ⊥) :
  ωStream.cases (a ::: x) cons bot = cons a x := by
  rw [ωStream.cases]
  simp [F.mk, Cons.cons]

inductive ωStream.eqF (r : ωStream α → ωStream α → Prop) :
  ωStream α → ωStream α → Prop where
| bot {a b} :
  ⊥ = a → ⊥ = b → eqF r a b
| cons {a b} (x : α) (xs ys: ωStream α) :
  x ::: xs = a → x ::: ys = b → r xs ys → eqF r a b

theorem ωStream.bisim (r : ωStream α → ωStream α → Prop)
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

def ωStream.dest.inj (k k': ωStream α) :
  k.dest = k'.dest → k = k' := by
  intro h
  apply bisim (λ k k' => k.dest = k'.dest) _ _ _ h
  intro s₁ s₂ h₁
  cases s₁ using ωStream.cases with
  | bot =>
    cases s₂ using ωStream.cases with
    | bot =>
      apply eqF.bot <;> rfl
    | cons y ys =>
      simp [Bot.bot, Cons.cons] at h₁
  | cons x xs =>
    cases s₂ using ωStream.cases with
    | bot =>
      simp [Bot.bot, Cons.cons] at h₁
    | cons y ys =>
      simp only [ωStream.dest_mk, Cons.cons, ωStream.F.cons.injEq] at h₁
      induction h₁.left
      induction h₁.right
      apply eqF.cons x xs xs
      · rfl
      · rfl
      · rfl

@[simp] def ωStream.dest.injEq (k k': ωStream α) :
  (k.dest = k'.dest) = (k = k') := by
  apply propext
  constructor
  · apply inj
  · apply congrArg


@[simp] def ωStream.mk_dest (k:ωStream α) : k.dest.mk = k := by
  apply dest.inj
  simp only [dest_mk]

def ωStream.cons.inj (x y: α) (xs ys: ωStream α) :
  x ::: xs = y ::: ys → x = y ∧ xs = ys := by
  intro h
  simp only [Cons.cons, F.mk.injEq, F.cons.injEq] at h
  assumption

def ωStream.cons.injEq (x y: α) (xs ys: ωStream α) :
  (x ::: xs = y ::: ys) = (x = y ∧ xs = ys) := by
  apply propext
  constructor
  · apply inj
  · intro h
    induction h.left
    induction h.right
    rfl


theorem ωStream.corec.unfold {β: Type v} (f: β → F α β) (x₀: β) :
  corec f x₀ =
      match f x₀ with
      | .cons x xs => x ::: (corec f xs)
      | .bot => ⊥ := by
  have := congrArg ωStream.F.mk (dest_corec f x₀)
  rw [mk_dest] at this
  rw [this]
  cases f x₀ with
  | bot =>
    rfl
  | cons x xs =>
    rfl

--attribute [eqns ωStream.corec.unfold] ωStream.corec

inductive ωStream.leF (r : ωStream α → ωStream α → Prop) :
  ωStream α → ωStream α → Prop where
| bot {a b} :
  ⊥ = a→ leF r a b
| cons {a b} (x : α) (xs ys: ωStream α) :
  x ::: xs = a → x ::: ys = b → r xs ys → leF r a b

-- A monotone version of the less than functor
def ωStream.leF.mono :
  (ωStream α → ωStream α → Prop) →o (ωStream α → ωStream α → Prop) where
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

instance ωStream.LEinst : LE (ωStream α) where
  le x y := pgfp ωStream.leF.mono ⊥ x y

#check pgfp.accumulate
#check pgfp.coinduction

theorem ωStream.le.coind (α: Type u) (P: ωStream α → ωStream α → Prop)
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

theorem ωStream.le.unfold {x y: ωStream α} :
  (x ≤ y) = leF (λ x y => x ≤ y) x y := by
  have := pgfp.unfold (@leF.mono α) ⊥
  conv =>
    lhs
    simp only [LE.le]
    rfl
  rw [←this]
  have : ∀ p:((_: ωStream α) × ωStream α → Prop), ⊥ ⊔ p = p := by
    intro p
    funext x
    simp
  simp only [this, CompleteLattice.bot_sup]
  rfl

@[simp] theorem ωStream.leF.mono.def
  (r: ωStream α → ωStream α → Prop) (x y: ωStream α) :
  leF.mono r x y = leF r x y := by rfl

-- proof of the Scott Continuity of `leF`
instance ωStream.leF.SC : ScottContinuousNat (@ωStream.leF.mono α) where
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
          simp only [Cons.cons, Bot.bot, F.mk.injEq] at h₂
        | cons a as bs eq₁ eq₂ h =>
          rw [cons.injEq] at eq₁
          rw [cons.injEq] at eq₂
          rw [←eq₁.right, ←eq₂.right]
          assumption

def ωStream.le.refl (x: ωStream α) : x ≤ x := by
  simp only [LE.le]
  coinduction generalizing [x] using ωStream.le.coind α
  intro a b ⟨x, h₁, h₂, h₃⟩; clear h₃
  induction h₁
  induction h₂
  cases x using ωStream.cases with
  | bot =>
    apply leF.bot
    rfl
  | cons x xs =>
    apply leF.cons x xs xs rfl rfl
    apply Or.inl
    exists xs

def ωStream.le.trans (x y z: ωStream α) : x ≤ y → y ≤ z → x ≤ z := by
  intro h₁ h₂
  coinduction generalizing [x, y, z] using ωStream.le.coind α
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
      simp [Bot.bot, Cons.cons] at h₄
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

instance : Preorder (ωStream α) where
  le_refl := ωStream.le.refl
  le_trans := ωStream.le.trans

@[mono]
def ωStream.bot_le (x: ωStream α) : ⊥ ≤ x := by
  rw [le.unfold]
  apply leF.bot rfl

instance {α: Type u} : OrderBot (ωStream α) where
  bot_le := ωStream.bot_le


def ωStream.le_bot (x: ωStream α) : x ≤ ⊥ → x = ⊥ := by
  intro h
  rw [le.unfold] at h
  cases h with
  | bot h =>
    exact Eq.symm h
  | cons x xs ys h₁ h₂ h₃ =>
    simp [Cons.cons, Bot.bot] at h₂

def ωStream.cons_le (x: α) (xs rhs: ωStream α) :
  (x ::: xs ≤ rhs) → {ys: ωStream α // rhs = x ::: ys ∧ xs ≤ ys} :=
  ωStream.cases rhs
    (cons := λ y ys h =>
      ⟨ys, by
        rw [le.unfold] at h
        cases h with
        | bot h =>
          simp [Cons.cons, Bot.bot] at h
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
      simp [Cons.cons, Bot.bot] at h'
    ))

def ωStream.le_cons (x y: α) (xs ys: ωStream α) :
  x ::: xs ≤ y ::: ys ↔ x = y ∧ xs ≤ ys := by
  constructor
  · intro h₁
    rw [le.unfold] at h₁
    cases h₁ with
    | bot h =>
      simp [Bot.bot, Cons.cons] at h
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
def ωStream.le_of_le_cons (x: α) (xs ys: ωStream α) :
  xs ≤ ys → x ::: xs ≤ x ::: ys := by
  rw [le_cons]
  trivial

inductive ωStream.findCons.Result (f: Nat →o ωStream α) : Type u where
| bot : (∀ n, f n = ⊥) → Result f
| cons (n:ℕ) (x: α) (g: Chain (ωStream α)) :
  (∀ k, x ::: g k = f (n+k)) → Result f

def ωStream.findCons.fromIndex
  {x xs} (f: Nat →o ωStream α) (n:Nat)
  (h₁: f n = x ::: xs) : Result f :=
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
  go : ∀ k, {xs: ωStream α // f (n+k) = x ::: xs} := λ k =>
    have h₂ : f n ≤ f (n+k) := by
      apply f.monotone'
      simp
    have ⟨ys, h₃, _⟩ := cons_le x xs (f <| n+k) (by rw [h₁] at h₂; exact h₂)
    ⟨ys, h₃⟩

def ωStream.findCons.exists (f: Nat →o ωStream α) : ∃ _: Result f, True := by
  by_cases h:(∀ n, f n = ⊥)
  · exists Result.bot h
  · rw [not_forall] at h
    have ⟨n, h⟩ := h
    revert h
    cases h:f n using ωStream.cases with
    | bot => simp [not_true]
    | cons x xs =>
      intro _
      apply Exists.intro (fromIndex f n h) True.intro

noncomputable def ωStream.findCons (f: Nat →o ωStream α) : findCons.Result f :=
  (Classical.indefiniteDescription _ (findCons.exists f)).val


noncomputable def ωStream.lub (f: Nat →o ωStream α) : ωStream α :=
  corec (λ f =>
    match findCons f with
    | .cons _ x xs _ =>
      .cons x xs
    | .bot _ => .bot
  ) f

theorem ωStream.lub.unfold (f: ℕ →o ωStream α) :
  lub f = match findCons f with
          | .cons _ x xs _ => x ::: lub xs
          | .bot _ => ⊥ := by
  rw [lub, corec.unfold]
  cases findCons f with
  | bot _ =>
    rfl
  | cons _ _ _ _ =>
    rfl

theorem ωStream.lub_le (f: ℕ →o ωStream α) (x: ωStream α)
  (hyp: ∀ n, f n ≤ x) : lub f ≤ x := by
  coinduction generalizing [f, x] using le.coind α
  intro a b ⟨f, x, lhs, rhs, hyp⟩
  induction lhs
  induction rhs
  clear a b
  rw [ωStream.lub.unfold]
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


theorem ωStream.le_lub
  (f: Nat →o ωStream α) (n: Nat) (X : ωStream α)
  (hX: X ≤ f n) : X ≤ lub f := by
  coinduction generalizing [X, n, f] using le.coind α
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
      simp [h₁, Bot.bot, Cons.cons] at h₂
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

noncomputable instance : OmegaCompletePartialOrder (ωStream α) where
  le_antisymm := by
    intro a b h₁ h₂
    coinduction generalizing [a, b] using ωStream.bisim
    intro s₁ s₂ ⟨a, b, eq₁, eq₂, h₁, h₂⟩
    induction eq₁
    induction eq₂
    rw [ωStream.le.unfold] at h₁
    cases h₁ with
    | bot h₁ =>
      induction h₁
      have := ωStream.le_bot _ h₂
      induction Eq.symm this
      induction h₂
      apply ωStream.eqF.bot rfl rfl
    | cons x xs ys eq₁ eq₂ h₁ =>
      induction eq₁
      induction eq₂
      rw [ωStream.le_cons] at h₂
      have h₃ := h₂.right
      apply ωStream.eqF.cons x xs ys rfl rfl
      exists xs
      exists ys

  ωSup := ωStream.lub

  ωSup_le f x h := ωStream.lub_le f x h
  le_ωSup f n := ωStream.le_lub f n (f n) (le_refl _)

theorem ωStream.ωSup.unfold (f: ℕ →o ωStream α) :
  ωSup f = match findCons f with
          | .cons _ x xs _ => x ::: ωSup xs
          | .bot _ => ⊥ :=
  lub.unfold f

theorem ωStream.ωSup_bot (f: ℕ →o ωStream α) :
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
    simp [Cons.cons, Bot.bot] at h'

#print ωStream.findCons.Result

theorem ωStream.ωSup_cons (f: ℕ →o ωStream α) :
  (n : ℕ) → (x : α) → (xs : ℕ →o ωStream α) →
  (∀ (k : ℕ), x ::: xs k = f (n + k)) →
  ωSup f = x ::: ωSup xs :=  by
  intro n x xs h₁
  rw [ωStream.ωSup.unfold f]
  cases findCons f with
  | bot h₂ =>
    specialize h₁ 0
    specialize h₂ n
    rw [Nat.add_zero, h₂] at h₁
    simp [Cons.cons, Bot.bot] at h₁
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

def OmegaCompletePartialOrder.Chain.offset
  [OmegaCompletePartialOrder α] (f: Chain α) (n: ℕ) : Chain α where
    toFun k := f (n+k)
    monotone' x y h₁ := f.monotone (by simp_arith [h₁])

def OmegaCompletePartialOrder.Chain.ωSup_offset
  [OmegaCompletePartialOrder α] (f: Chain α) (n: ℕ) :
  ωSup (f.offset n) = ωSup f := by
  apply le_antisymm
  <;> apply ωSup_le
  <;> intro m
  · apply le_ωSup f (n+m)
  · calc
      f m ≤ f (n + m) := f.monotone (by simp_arith)
      _ ≤ f.offset n m := le_refl _
      _ ≤ _ := le_ωSup _ _



def ωStream.findCons.Result.offset (m: ℕ) (f: ℕ →o ωStream α)
  (n : ℕ) (x : α) (xs : Chain (ωStream α))
  (hyp: ∀ (k : ℕ), x ::: xs k = f (n + k)) :
  {ys: Chain (ωStream α) // ∀ k, x ::: ys k = f ((n + m) + k)} where
  val := xs.offset m
  property k := by
    rw [OmegaCompletePartialOrder.Chain.offset, OrderHom.mk_apply, hyp]
    apply congrArg f
    simp_arith

#check ωStream.corec
#print ωStream.F
def ωStream.fst {α: Type u} {β: Type v} (k: ωStream (α × β)) : ωStream α :=
  corec
    (fun k => ωStream.cases k (cons:= λ x xs => F.cons x.fst xs) (bot := F.bot)) k

@[simp] theorem ωStream.fst.unfold_bot {α: Type u} {β: Type v} :
  @ωStream.fst α β ⊥ = ⊥ := by
  rw [fst, corec.unfold, ωStream.cases_bot]

@[simp] theorem ωStream.fst.unfold_cons
  {α: Type u} {β: Type v} (x: α × β) (xs : ωStream (α × β)) :
  @ωStream.fst α β (x ::: xs) = x.fst ::: xs.fst := by
  rw [fst, corec.unfold, ωStream.cases_cons, cons.injEq]
  trivial

--attribute [eqns ωStream.fst.unfold_cons ωStream.fst.unfold_bot] ωStream.fst

@[mono]
theorem ωStream.fst.monotone {α: Type u} {β: Type v} :
  ∀ x y: ωStream (α × β), x ≤ y → x.fst ≤ y.fst := by
  intro a b h₁
  coinduction generalizing [a, b] using ωStream.le.coind α
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
def OrderHom.ωStream.fst {α: Type u} {β: Type v} :
  ωStream (α × β) →o ωStream α where
  toFun := _root_.ωStream.fst
  monotone' {x y} h := ωStream.fst.monotone x y h

#check ωStream.ωSup_bot
#check ωStream.ωSup_cons

theorem ωStream.fst.continuous {α: Type u} {β: Type v} :
  OmegaCompletePartialOrder.Continuous (@OrderHom.ωStream.fst α β) := by
  intro chain
  unfold OrderHom.ωStream.fst
  coinduction generalizing [chain] using ωStream.bisim
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
      simp only [Chain.map, OrderHom.comp_coe, OrderHom.coe_mk,
        Function.comp_apply, h, unfold_bot]
  | cons n x xs h =>
    apply
      eqF.cons x.fst (ωSup xs).fst (ωSup (OrderHom.comp ⟨fst, fst.monotone⟩ xs))
    · rw [ωSup_cons chain n x xs, OrderHom.mk_apply, fst.unfold_cons]
      assumption
    · conv =>
        rhs
        rw [ωSup_cons _ n x.fst (OrderHom.comp ⟨fst, fst.monotone⟩ xs)]
        rfl
        tactic =>
          intro m
          simp only [OrderHom.comp_coe, OrderHom.coe_mk,
            Function.comp_apply, Chain.map]
          rw [←h m]
          simp [unfold_cons]
    · exists xs

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.ωStream.fst
  {α: Type u} {β: Type v} : ωStream (α × β) →𝒄 ωStream α where
  toFun := _root_.ωStream.fst
  monotone' := OrderHom.ωStream.fst.monotone
  cont := ωStream.fst.continuous

def ωStream.snd {α: Type u} {β: Type v} (k: ωStream (α × β)) : ωStream β :=
  corec
    (fun k => ωStream.cases k (cons:= λ  x xs => F.cons x.snd xs) (bot := F.bot))
    k

@[simp] theorem ωStream.snd.unfold_bot {α: Type u} {β: Type v} :
  @ωStream.snd α β ⊥ = ⊥ := by
  rw [snd, corec.unfold, ωStream.cases_bot]

@[simp] theorem ωStream.snd.unfold_cons
  {α: Type u} {β: Type v} (x: α × β) (xs : ωStream (α × β)) :
  @ωStream.snd α β (x ::: xs) = x.snd ::: xs.snd := by
  rw [snd, corec.unfold, ωStream.cases_cons, cons.injEq]
  trivial

--attribute [eqns ωStream.snd.unfold_cons ωStream.snd.unfold_bot] ωStream.snd

@[mono]
theorem ωStream.snd.monotone {α: Type u} {β: Type v} :
  ∀ x y: ωStream (α × β), x ≤ y → x.snd ≤ y.snd := by
  intro a b h₁
  coinduction generalizing [a, b] using ωStream.le.coind β
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
def OrderHom.ωStream.snd {α: Type u} {β: Type v} :
  ωStream (α × β) →o ωStream β where
  toFun := _root_.ωStream.snd
  monotone' {x y} h := ωStream.snd.monotone x y h

theorem ωStream.snd.continuous {α: Type u} {β: Type v} :
  OmegaCompletePartialOrder.Continuous (@OrderHom.ωStream.snd α β) := by
  unfold OrderHom.ωStream.snd
  intro chain
  coinduction generalizing [chain] using ωStream.bisim
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
      simp only [Chain.map, OrderHom.comp_coe, OrderHom.coe_mk,
        Function.comp_apply, h, unfold_bot]
  | cons n x xs h =>
    apply eqF.cons x.snd (ωSup xs).snd
      (ωSup (OrderHom.comp ⟨snd, snd.monotone⟩ xs))
    · rw [ωSup_cons chain n x xs, OrderHom.mk_apply, snd.unfold_cons]
      assumption
    · conv =>
        rhs
        rw [ωSup_cons _ n x.snd (OrderHom.comp ⟨snd, snd.monotone⟩ xs)]
        rfl
        tactic =>
          intro m
          simp only
            [OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, Chain.map]
          rw [←h m]
          simp [unfold_cons]
    · exists xs

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.ωStream.snd
  {α: Type u} {β: Type u} : ωStream (α × β) →𝒄 ωStream β where
  toFun := _root_.ωStream.snd
  monotone' := ωStream.snd.monotone
  cont := ωStream.snd.continuous


def ωStream.tup {α: Type u} {β: Type v}
  (k₁: ωStream α) (k₂: ωStream β) : ωStream (α × β) :=
  corec (fun (x, y) =>
    match dest x, dest y with
    | .bot, _ => F.bot
    | _, .bot => F.bot
    | .cons x xs, .cons y ys => .cons (x, y) (xs, ys)
  ) (k₁, k₂)

@[simp] theorem ωStream.tup.unfold_bot_left
  {α: Type u} {β: Type v} (k₂: ωStream β) :
  @tup α β ⊥ k₂ = ⊥ := by
  rw [tup, corec.unfold]
  simp [dest_bot]

@[simp] theorem ωStream.tup.unfold_bot_right
  {α: Type u} {β: Type v} (k₁: ωStream α) :
  @tup α β k₁ ⊥ = ⊥ := by
  rw [tup, corec.unfold]
  simp [dest_bot]
  cases dest k₁ <;> rfl

@[simp] theorem ωStream.tup.unfold_cons
  {α: Type u} {β: Type v} (x: α) (xs: ωStream α) (y: β) (ys: ωStream β) :
  @tup α β (x ::: xs) (y ::: ys) = (x, y) ::: tup xs ys := by
  rw [tup, corec.unfold]
  have h₁ : dest (x ::: xs) = .cons x xs := by rfl
  have h₂ : dest (y ::: ys) = .cons y ys := by rfl
  simp only [h₁, h₂]
  rfl

--attribute [eqns ωStream.tup.unfold_cons ωStream.tup.unfold_bot_left ωStream.tup.unfold_bot_right] ωStream.tup

@[simp] theorem ωStream.tup_fst_snd
  {α: Type u} {β: Type v} (k: ωStream (α × β)) :
  tup k.fst k.snd = k := by
  coinduction generalizing [k] using bisim
  intro s₁ s₂ ⟨x, h₁, h₂, _⟩
  induction h₁
  cases x with
  | bot =>
    simp only [fst.unfold_bot, tup.unfold_bot_left] at h₂
    induction h₂
    apply eqF.bot rfl rfl
  | cons x xs =>
    simp only
      [fst.unfold_cons, snd.unfold_cons, tup.unfold_cons, Prod.mk.eta] at h₂
    induction h₂
    apply eqF.cons x (tup xs.fst xs.snd) xs rfl rfl
    exists xs

@[mono] theorem ωStream.tup.monotone {α: Type u} {β: Type v} :
  ∀ (x y: ωStream α) (z w: ωStream β), x ≤ y → z ≤ w → tup x z ≤ tup y w := by
  intro x y z w h₁ h₂
  coinduction generalizing [x, y, z, w] using ωStream.le.coind _
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
def OrderHom.ωStream.tup {α: Type u} {β: Type v} :
  ωStream α →o ωStream β →o ωStream (α × β) :=
  OrderHom.curry
    { toFun := λ (x, y) => _root_.ωStream.tup x y
    , monotone' := λ _ _ h => ωStream.tup.monotone _ _ _ _ h.left h.right}

def ωStream.tup.continuous {α : Type u} {β: Type v} :
  OmegaCompletePartialOrder.Continuous
    (OrderHom.curry.symm (@OrderHom.ωStream.tup α β)) := by
  intro chain
  simp only [OrderIso.symm, OrderHom.curry, OrderHom.ωStream.tup, RelIso.coe_fn_mk,
    Equiv.coe_fn_mk, OrderHom.coe_mk, RelIso.coe_fn_symm_mk,
    Equiv.coe_fn_symm_mk, OrderHom.mk_apply, Function.uncurry_curry,
    Prod.instOmegaCompletePartialOrder_ωSup_fst,
    Prod.instOmegaCompletePartialOrder_ωSup_snd]
  have ⟨(lhs, rhs), h₁⟩ :
    {p: Chain (ωStream α) × Chain (ωStream β) // p.fst.zip p.snd = chain} :=
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
  coinduction generalizing [lhs, rhs] using ωStream.bisim
  let monoTup : ωStream α × ωStream β →o ωStream (α × β) :=
    ⟨λ p => p.1.tup p.2, λ (x, y) (z, t) h => tup.monotone x z y t h.left h.right⟩
  intro s₁ s₂ ⟨lhs, rhs, eq₁, eq₂, _⟩
  induction eq₁
  induction eq₂
  cases findCons lhs with
  | bot h₁ =>
    apply eqF.bot
    rw [ωSup_bot lhs]
    · rw [ωStream.tup.unfold_bot_left]
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
      · rw [ωStream.tup.unfold_bot_right]
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
def OmegaCompletePartialOrder.ContinuousHom.ωStream.tup {α: Type u} {β: Type v} :
  ωStream α × ωStream β →𝒄 ωStream (α × β) where
  toFun := λ (x, y) => _root_.ωStream.tup x y
  monotone' := λ _ _ ⟨h₁, h₂⟩ => ωStream.tup.monotone _ _ _ _ h₁ h₂
  cont := ωStream.tup.continuous

#check ωStream.ωSup_cons


def ωStream.fby (x y: ωStream α) : ωStream α :=
  ωStream.cases x (cons := λ x _ => x ::: y) (bot := ⊥)

@[simp] def ωStream.fby.unfold_bot (x: ωStream α) : fby ⊥ x = ⊥ := by
  rw [fby, ωStream.cases_bot]

@[simp] def ωStream.fby.unfold_cons (x : α) (xs y: ωStream α) :
  fby (x ::: xs) y = x ::: y := by
  rw [fby, ωStream.cases_cons]

--attribute [eqns ωStream.fby.unfold_bot ωStream.fby.unfold_cons] ωStream.fby

@[mono]
theorem ωStream.fby.monotone (x y z w: ωStream α) :
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
def OrderHom.ωStream.fby : ωStream α →o ωStream α →o ωStream α :=
  OrderHom.curry
    {toFun := λ (x, y) => _root_.ωStream.fby x y
    , monotone' := λ  _ _ ⟨h₁, h₂⟩ => ωStream.fby.monotone _ _ _ _ h₁ h₂}


def ωStream.fby.continuous :
  OmegaCompletePartialOrder.Continuous
    (OrderHom.curry.symm (@OrderHom.ωStream.fby α)) := by
  intro chain
  simp only [OrderHom.ωStream.fby, OrderIso.symm_apply_apply, OrderHom.mk_apply,
    Prod.instOmegaCompletePartialOrder_ωSup_fst,
    Prod.instOmegaCompletePartialOrder_ωSup_snd]
  let ⟨(lhs, rhs), h₁⟩ : {p: Chain (ωStream α) × Chain (ωStream α) // p.fst.zip p.snd = chain} :=
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
def OmegaCompletePartialOrder.ContinuousHom.ωStream.fby
  : ωStream α × ωStream α →𝒄 ωStream α where
  toFun := λ (x, y) => _root_.ωStream.fby x y
  monotone' := λ _ _ ⟨h₁, h₂⟩ => ωStream.fby.monotone _ _ _ _ h₁ h₂
  cont := ωStream.fby.continuous

def ωStream.map {α: Type u} {β: Type v} (f: α → β) (x: ωStream α) : ωStream β :=
  ωStream.corec (λ x =>
      ωStream.cases x (cons := λ x xs =>
        .cons (f x) xs
      ) (bot := .bot)
    ) x

@[simp] def ωStream.map.unfold_bot {α: Type u} {β: Type v} (f: α → β) :
  map f ⊥ = ⊥ := by
  rw [map, corec.unfold, ωStream.cases_bot]

@[simp] def ωStream.map.unfold_cons
  {α: Type u} {β: Type v} (f: α → β) (x: α) (xs: ωStream α) :
  map f (x ::: xs) = f x ::: map f xs := by
  rw [map, corec.unfold, ωStream.cases_cons]
  rfl

--attribute [eqns ωStream.map.unfold_bot ωStream.map.unfold_cons] ωStream.map

@[mono] theorem ωStream.map.monotone {α: Type u} {β: Type v} (f: α → β) :
  ∀ x y, x ≤ y → map f x ≤ map f y := by
  intro x y h₁
  coinduction generalizing [x, y] using ωStream.le.coind _
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
def OrderHom.ωStream.map {α: Type u} {β: Type v} (f: α → β) :
  ωStream α →o ωStream β where
  toFun := _root_.ωStream.map f
  monotone' := ωStream.map.monotone f

def ωStream.map.continuous {α: Type u} {β: Type v} (f: α → β) :
  OmegaCompletePartialOrder.Continuous (OrderHom.ωStream.map f) := by
  intro chain
  unfold OrderHom.ωStream.map
  coinduction generalizing [chain] using ωStream.bisim
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
    apply eqF.cons
      (f x) (map f (ωSup xs))
      (ωSup (xs.map ⟨ωStream.map f, ωStream.map.monotone f⟩))
    · rw [OrderHom.mk_apply, ωSup_cons chain n x xs]
      · rw [map.unfold_cons]
      · assumption
    · rw [ωSup_cons (chain.map _) n (f x) (xs.map ⟨map f, map.monotone f⟩)]
      simp only
        [Chain.map, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply]
      intro k
      rw [←h₁ k, map.unfold_cons]
    · exists xs

@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.ωStream.map
  {α: Type u} {β: Type v} (f: α → β) : ωStream α →𝒄 ωStream β where
  toFun := _root_.ωStream.map f
  monotone' := ωStream.map.monotone f
  cont := ωStream.map.continuous f

def ωStream.const (x: α) : ωStream α :=
  corec (λ _ => .cons x Unit.unit) Unit.unit

def ωStream.const.unfold (x: α) : const x = (x ::: const x) := by
  conv =>
    lhs
    simp only [const]
    rw [corec.unfold]
    rfl
  rfl


-- Addition of kahn networks
instance {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ] :
  HAdd (ωStream α) (ωStream β) (ωStream γ) where
  hAdd k₁ k₂ := ωStream.map (Function.uncurry HAdd.hAdd) (ωStream.tup k₁ k₂)

@[simp] def ωStream.add.unfold_bot_left
  {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ] (x: ωStream β) :
  (⊥ : ωStream α) + x = ⊥ := by simp [HAdd.hAdd]

@[simp] def ωStream.add.unfold_bot_right
  {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ] (x: ωStream α) :
  x + (⊥ : ωStream β) = ⊥ := by simp [HAdd.hAdd]

@[simp] def ωStream.add.unfold_cons
  {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ]
  (x: α) (xs: ωStream α) (y: β) (ys: ωStream β) :
  (x ::: xs) + (y ::: ys) = (x + y) ::: (xs + ys) := by simp [HAdd.hAdd]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.add
  {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ] :
  ωStream α × ωStream β →𝒄 ωStream γ :=
  (ContinuousHom.ωStream.map (Function.uncurry HAdd.hAdd)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.add_apply
  {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ]
  (x: ωStream α) (y: ωStream β) : ContinuousHom.ωStream.add (x, y) = x + y
  := rfl




-- Substraction of kahn networks
instance {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ] :
  HSub (ωStream α) (ωStream β) (ωStream γ) where
  hSub k₁ k₂ := ωStream.map (Function.uncurry HSub.hSub) (ωStream.tup k₁ k₂)

@[simp] def ωStream.sub.unfold_bot_left
  {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ] (x: ωStream β) :
  (⊥ : ωStream α) - x = ⊥ := by simp [HSub.hSub]

@[simp] def ωStream.sub.unfold_bot_right
  {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ] (x: ωStream α) :
  x - (⊥ : ωStream β) = ⊥ := by simp [HSub.hSub]

@[simp] def ωStream.sub.unfold_cons
  {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ]
  (x: α) (xs: ωStream α) (y: β) (ys: ωStream β) :
  (x ::: xs) - (y ::: ys) = (x - y) ::: (xs - ys) := by simp [HSub.hSub]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.sub
  {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ]
  : ωStream α × ωStream β →𝒄 ωStream γ :=
  (ContinuousHom.ωStream.map (Function.uncurry HSub.hSub)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.sub_apply
  {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ]
  (x: ωStream α) (y: ωStream β) : ContinuousHom.ωStream.sub (x, y) = x - y
  := rfl





-- Multiplication of kahn networks
instance {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ] :
  HMul (ωStream α) (ωStream β) (ωStream γ) where
  hMul k₁ k₂ := ωStream.map (Function.uncurry HMul.hMul) (ωStream.tup k₁ k₂)

@[simp] def ωStream.mul.unfold_bot_left
  {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ] (x: ωStream β) :
  (⊥ : ωStream α) * x = ⊥ := by simp [HMul.hMul]

@[simp] def ωStream.mul.unfold_bot_right
  {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ] (x: ωStream α) :
  x * (⊥ : ωStream β) = ⊥ := by simp [HMul.hMul]

@[simp] def ωStream.mul.unfold_cons
  {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ]
  (x: α) (xs: ωStream α) (y: β) (ys: ωStream β) :
  (x ::: xs) * (y ::: ys) = (x * y) ::: (xs * ys) := by simp [HMul.hMul]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.mul
  {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ]
  : ωStream α × ωStream β →𝒄 ωStream γ :=
  (ContinuousHom.ωStream.map (Function.uncurry HMul.hMul)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.mul_apply
  {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ]
  (x: ωStream α) (y: ωStream β) : ContinuousHom.ωStream.mul (x, y) = x * y
  := rfl



-- Division of kahn networks
instance {α: Type u} {β: Type v} {γ: Type w} [HDiv α β γ] :
  HDiv (ωStream α) (ωStream β) (ωStream γ) where
  hDiv k₁ k₂ := ωStream.map (Function.uncurry HDiv.hDiv) (ωStream.tup k₁ k₂)

@[simp] def ωStream.div.unfold_bot_left
  {α: Type u} {β: Type v} {γ: Type w} [HDiv α β γ] (x: ωStream β) :
  (⊥ : ωStream α) / x = ⊥ := by simp [HDiv.hDiv]

@[simp] def ωStream.div.unfold_bot_right
  {α: Type u} {β: Type v} {γ: Type w} [HDiv α β γ] (x: ωStream α) :
  x / (⊥ : ωStream β) = ⊥ := by simp [HDiv.hDiv]

@[simp] def ωStream.div.unfold_cons
  {α: Type u} {β: Type v} {γ: Type w}
  [HDiv α β γ] (x: α) (xs: ωStream α) (y: β) (ys: ωStream β) :
  (x ::: xs) / (y ::: ys) = (x / y) ::: (xs / ys) := by simp [HDiv.hDiv]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.div
  {α: Type u} {β: Type v} {γ: Type w} [HDiv α β γ] :
  ωStream α × ωStream β →𝒄 ωStream γ :=
  (ContinuousHom.ωStream.map (Function.uncurry HDiv.hDiv)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.div_apply
  {α: Type u} {β: Type v} {γ: Type w} [HDiv α β γ]
  (x: ωStream α) (y: ωStream β) : ContinuousHom.ωStream.div (x, y) = x / y
  := rfl



-- Modular arithmetic over kahn networks
instance {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ] :
  HMod (ωStream α) (ωStream β) (ωStream γ) where
  hMod k₁ k₂ := ωStream.map (Function.uncurry HMod.hMod) (ωStream.tup k₁ k₂)

@[simp] def ωStream.mod.unfold_bot_left
  {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ] (x: ωStream β) :
  (⊥ : ωStream α) % x = ⊥ := by simp [HMod.hMod]

@[simp] def ωStream.mod.unfold_bot_right
  {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ] (x: ωStream α) :
  x % (⊥ : ωStream β) = ⊥ := by simp [HMod.hMod]

@[simp] def ωStream.mod.unfold_cons
  {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ]
  (x: α) (xs: ωStream α) (y: β) (ys: ωStream β) :
  (x ::: xs) % (y ::: ys) = (x % y) ::: (xs % ys) := by simp [HMod.hMod]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.mod
  {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ] :
  ωStream α × ωStream β →𝒄 ωStream γ :=
  (ContinuousHom.ωStream.map (Function.uncurry HMod.hMod)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.mod_apply
  {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ]
  (x: ωStream α) (y: ωStream β) : ContinuousHom.ωStream.mod (x, y) = x % y
  := rfl


def ωStream.and : ωStream Prop → ωStream Prop → ωStream Prop := λ k₁ k₂ =>
  ωStream.map (Function.uncurry And) (ωStream.tup k₁ k₂)

@[simp] def ωStream.and.unfold_bot_left (x: ωStream Prop) :
  ωStream.and ⊥ x = ⊥ := by simp [ωStream.and]

@[simp] def ωStream.and.unfold_bot_right (x: ωStream Prop) :
  ωStream.and x ⊥ = ⊥ := by simp [ωStream.and]

@[simp] def ωStream.and.unfold_cons
  (x: Prop) (xs: ωStream Prop) (y: Prop) (ys: ωStream Prop) :
  ωStream.and (x ::: xs) (y ::: ys) = (x ∧ y) ::: ωStream.and xs ys
  := by simp [ωStream.and]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.and
  : ωStream Prop × ωStream Prop →𝒄 ωStream Prop :=
  (ContinuousHom.ωStream.map (Function.uncurry And)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.and_apply
  (x: ωStream Prop) (y: ωStream Prop) :
  ContinuousHom.ωStream.and (x, y) = _root_.ωStream.and x y
  := rfl



def ωStream.not : ωStream Prop → ωStream Prop := λ k₁ =>
  ωStream.map Not k₁

@[simp] def ωStream.not.unfold_bot :
  ωStream.not ⊥ = ⊥ := by simp [ωStream.not]

@[simp] def ωStream.not.unfold_cons (x: Prop) (xs: ωStream Prop) :
  ωStream.not (x ::: xs) = (¬x) ::: ωStream.not xs := by simp [ωStream.not]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.not :
  ωStream Prop →𝒄 ωStream Prop :=
  map Not

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.not_apply
  (x: ωStream Prop) : ContinuousHom.ωStream.not x = _root_.ωStream.not x
  := rfl




def ωStream.or : ωStream Prop → ωStream Prop → ωStream Prop := λ k₁ k₂ =>
  ωStream.map (Function.uncurry Or) (ωStream.tup k₁ k₂)

@[simp] def ωStream.or.unfold_bot_left (x: ωStream Prop) :
  ωStream.or ⊥ x = ⊥ := by simp [ωStream.or]

@[simp] def ωStream.or.unfold_bot_right (x: ωStream Prop) :
  ωStream.or x ⊥ = ⊥ := by simp [ωStream.or]

@[simp] def ωStream.or.unfold_cons
  (x: Prop) (xs: ωStream Prop) (y: Prop) (ys: ωStream Prop) :
  ωStream.or (x ::: xs) (y ::: ys) = (x ∨ y) ::: ωStream.or xs ys
  := by simp [ωStream.or]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.or
  : ωStream Prop × ωStream Prop →𝒄 ωStream Prop :=
  (ContinuousHom.ωStream.map (Function.uncurry Or)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.or_apply
  (x: ωStream Prop) (y: ωStream Prop) :
  ContinuousHom.ωStream.or (x, y) = _root_.ωStream.or x y
  := rfl





def ωStream.eq : ωStream α → ωStream α → ωStream Prop := λ k₁ k₂ =>
  ωStream.map (Function.uncurry Eq) (ωStream.tup k₁ k₂)

@[simp] def ωStream.eq.unfold_bot_left (x: ωStream α) :
  ωStream.eq ⊥ x = ⊥ := by simp [ωStream.eq]

@[simp] def ωStream.eq.unfold_bot_right (x: ωStream α) :
  ωStream.eq x ⊥ = ⊥ := by simp [ωStream.eq]

@[simp] def ωStream.eq.unfold_cons
  (x: α) (xs: ωStream α) (y: α) (ys: ωStream α) :
  ωStream.eq (x ::: xs) (y ::: ys) = (x = y) ::: ωStream.eq xs ys
  := by simp [ωStream.eq]

def OmegaCompletePartialeqder.ContinuousHom.ωStream.eq :
  ωStream α × ωStream α →𝒄 ωStream Prop :=
  (ContinuousHom.ωStream.map (Function.uncurry Eq)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialeqder.ContinuousHom.ωStream.eq_apply
  (x: ωStream α) (y: ωStream α) :
  ContinuousHom.ωStream.eq (x, y) = _root_.ωStream.eq x y
  := rfl





def ωStream.le [LE α] : ωStream α → ωStream α → ωStream Prop := λ k₁ k₂ =>
  ωStream.map (Function.uncurry LE.le) (ωStream.tup k₁ k₂)

@[simp] def ωStream.le.unfold_bot_left [LE α] (x: ωStream α) :
  ωStream.le ⊥ x = ⊥ := by simp [ωStream.le]

@[simp] def ωStream.le.unfold_bot_right [LE α] (x: ωStream α) :
  ωStream.le x ⊥ = ⊥ := by simp [ωStream.le]

@[simp] def ωStream.le.unfold_cons [LE α]
  (x: α) (xs: ωStream α) (y: α) (ys: ωStream α) :
  ωStream.le (x ::: xs) (y ::: ys) = (x ≤ y) ::: ωStream.le xs ys
  := by simp [ωStream.le]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.le [LE α] :
  ωStream α × ωStream α →𝒄 ωStream Prop :=
  (ContinuousHom.ωStream.map (Function.uncurry LE.le)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.le_apply [LE α]
  (x: ωStream α) (y: ωStream α) :
  ContinuousHom.ωStream.le (x, y) = _root_.ωStream.le x y
  := rfl

@[simp] def ωStream.ge [LE α] (x y: ωStream α) := ωStream.le y x

def OmegaCompletePartialOrder.ContinuousHom.ωStream.ge [LE α] :
  ωStream α × ωStream α →𝒄 ωStream Prop :=
  ContinuousHom.ωStream.le.comp
    (ContinuousHom.Prod.prod ContinuousHom.Prod.snd ContinuousHom.Prod.fst)

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.ge_apply [LE α]
  (x: ωStream α) (y: ωStream α) :
  ContinuousHom.ωStream.ge (x, y) = _root_.ωStream.ge x y
  := rfl





def ωStream.lt [LT α] : ωStream α → ωStream α → ωStream Prop := λ k₁ k₂ =>
  ωStream.map (Function.uncurry LT.lt) (ωStream.tup k₁ k₂)

@[simp] def ωStream.lt.unfold_bot_left [LT α] (x: ωStream α) :
  ωStream.lt ⊥ x = ⊥ := by simp [ωStream.lt]

@[simp] def ωStream.lt.unfold_bot_right [LT α] (x: ωStream α) :
  ωStream.lt x ⊥ = ⊥ := by simp [ωStream.lt]

@[simp] def ωStream.lt.unfold_cons [LT α]
  (x: α) (xs: ωStream α) (y: α) (ys: ωStream α) :
  ωStream.lt (x ::: xs) (y ::: ys) = (x < y) ::: ωStream.lt xs ys
  := by simp [ωStream.lt]

def OmegaCompletePartialOrder.ContinuousHom.ωStream.lt [LT α] :
  ωStream α × ωStream α →𝒄 ωStream Prop :=
  (ContinuousHom.ωStream.map (Function.uncurry LT.lt)).comp
    ContinuousHom.ωStream.tup

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.lt_apply [LT α]
  (x: ωStream α) (y: ωStream α) :
  ContinuousHom.ωStream.lt (x, y) = _root_.ωStream.lt x y
  := rfl

@[simp] def ωStream.gt [LT α] (x y: ωStream α) := ωStream.lt y x

def OmegaCompletePartialOrder.ContinuousHom.ωStream.gt [LT α] :
  ωStream α × ωStream α →𝒄 ωStream Prop :=
  ContinuousHom.ωStream.lt.comp
    (ContinuousHom.Prod.prod ContinuousHom.Prod.snd ContinuousHom.Prod.fst)

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.gt_apply [LT α]
  (x: ωStream α) (y: ωStream α) :
  ContinuousHom.ωStream.gt (x, y) = _root_.ωStream.gt x y
  := rfl






-- Defintion of mux (if then else operators) over kahn networks
noncomputable def ωStream.mux (x: ωStream Prop) (y z: ωStream α) : ωStream α :=
  ωStream.map
    (λ ⟨a, b, c⟩ => @ite _ a (Classical.propDecidable a) b c)
    (ωStream.tup x (ωStream.tup y z))

@[simp] def ωStream.mux.unfold_bot_cond
  (y z: ωStream α) : ωStream.mux ⊥ y z = ⊥ :=
  by simp [ωStream.mux]

@[simp] def ωStream.mux.unfold_bot_left (x: ωStream Prop) (z: ωStream α)
  : ωStream.mux x ⊥ z = ⊥ := by
  simp [ωStream.mux]

@[simp] def ωStream.mux.unfold_bot_right (x: ωStream Prop) (y: ωStream α) :
  ωStream.mux x y ⊥ = ⊥ := by
  simp [ωStream.mux]

@[simp] def ωStream.mux.unfold_cons_true
  (y z: α) (xs: ωStream Prop) (ys zs: ωStream α) :
  ωStream.mux (True ::: xs) (y ::: ys) (z ::: zs) = y ::: (xs.mux ys zs) := by
  simp [ωStream.mux]

@[simp] def ωStream.mux.unfold_cons_false
  (y z: α) (xs: ωStream Prop) (ys zs: ωStream α) :
  ωStream.mux (False ::: xs) (y ::: ys) (z ::: zs) = z ::: (xs.mux ys zs) := by
  simp [ωStream.mux]

noncomputable def OmegaCompletePartialOrder.ContinuousHom.ωStream.mux :
  ωStream Prop × ωStream α × ωStream α →𝒄 ωStream α :=
  (ContinuousHom.ωStream.map
    (λ ⟨a, b, c⟩ => @ite _ a (Classical.propDecidable a) b c)).comp (
    ContinuousHom.ωStream.tup.comp (ContinuousHom.Prod.prod
      ContinuousHom.Prod.fst
      (ContinuousHom.ωStream.tup.comp ContinuousHom.Prod.snd)
    ))

@[simp] def OmegaCompletePartialOrder.ContinuousHom.ωStream.mux_apply
  (x: ωStream Prop) (y z: ωStream α) :
  ContinuousHom.ωStream.mux (x, y, z) = x.mux y z
  := rfl


def ωStream.next (x: ωStream α) : ωStream α :=
  ωStream.cases (bot := .bot) (cons := λ _ xs => xs) x

@[simp] def ωStream.next.unfold_bot : ωStream.next (⊥: ωStream α) = ⊥ := by
  rw [ωStream.next, ωStream.cases_bot]

@[simp] def ωStream.next.unfold_cons (x: α) (xs: ωStream α) :
  ωStream.next (x ::: xs) = xs := by
  rw [ωStream.next, ωStream.cases_cons]

#check ωStream.F.mk.inj

@[simps! coe]
def OrderHom.ωStream.next : ωStream α →o ωStream α where
  toFun := _root_.ωStream.next
  monotone' := by
    intro x y h₁
    cases x with
    | bot =>
      simp
    | cons x xs =>
      cases y with
      | bot =>
        rw [ωStream.le_bot _ h₁]
      | cons y ys =>
        rw [ωStream.le_cons x y xs ys] at h₁
        simp only [ωStream.next.unfold_cons]
        apply h₁.right

#check Preorder.le_trans

def OmegaCompletePartialOrder.ContinuousHom.ωStream.next :
  ωStream α →𝒄 ωStream α where
  toFun := _root_.ωStream.next
  monotone' := OrderHom.ωStream.next.monotone'
  cont := by
    intro chain
    simp
    apply le_antisymm
    · cases ωStream.findCons chain with
      | bot h₁ =>
        rw [ωStream.ωSup_bot chain h₁]
        rw [ωStream.ωSup_bot]
        · simp
        · intro n
          simp [Chain.map, h₁ n]
      | cons n x xs h₁ =>
        rw [ωStream.ωSup_cons chain n x xs h₁]
        apply ωSup_le
        intro m
        apply Preorder.le_trans _ _ _ _ (le_ωSup _ (n+m))
        simp [←h₁ m]
    · apply ωSup_le
      intro n
      apply OrderHom.ωStream.next.monotone
      apply le_ωSup




def ωStream.first (x: ωStream α) : ωStream α :=
  ωStream.cases (bot := .bot) (cons := λ x _ => const x) x

@[simp] def ωStream.first.unfold_bot : ωStream.first (⊥: ωStream α) = ⊥ := by
  rw [ωStream.first, ωStream.cases_bot]

@[simp] def ωStream.first.unfold_cons
  (x: α) (xs: ωStream α) : ωStream.first (x ::: xs) = const x := by
  rw [ωStream.first, ωStream.cases_cons]

@[simps! coe]
def OrderHom.ωStream.first : ωStream α →o ωStream α where
  toFun := _root_.ωStream.first
  monotone' := by
    intro x y h₁
    cases x with
    | bot =>
      simp
    | cons x xs =>
      cases y with
      | bot =>
        rw [ωStream.le_bot _ h₁]
      | cons y ys =>
        rw [ωStream.le_cons x y xs ys] at h₁
        simp only [ωStream.first.unfold_cons]
        rw [h₁.left]

#check Preorder.le_trans

def OmegaCompletePartialOrder.ContinuousHom.ωStream.first
  : ωStream α →𝒄 ωStream α where
  toFun := _root_.ωStream.first
  monotone' := OrderHom.ωStream.first.monotone'
  cont := by
    intro chain
    simp
    apply le_antisymm
    · cases ωStream.findCons chain with
      | bot h₁ =>
        rw [ωStream.ωSup_bot chain h₁]
        rw [ωStream.ωSup_bot]
        · simp
        · intro n
          simp [Chain.map, h₁ n]
      | cons n x xs h₁ =>
        conv =>
          congr
          · rw [ωStream.ωSup_cons chain n x xs h₁]
          · rw [ωStream.ωSup_cons _ n x (OrderHom.const _ (ωStream.const x))]
            rfl
            tactic =>
              intro m
              simp [Chain.map, ←h₁ m, ←ωStream.const.unfold]
        simp
        have : ωSup (OrderHom.const _ (ωStream.const x)) = ωStream.const x := by
          apply le_antisymm
          · apply ωSup_le
            intro n
            apply le_refl
          · apply le_ωSup (OrderHom.const _ (ωStream.const x)) n
        rw [this]
        conv =>
          lhs
          rw [ωStream.const.unfold]
    · apply ωSup_le
      intro n
      apply OrderHom.ωStream.first.monotone
      apply le_ωSup


