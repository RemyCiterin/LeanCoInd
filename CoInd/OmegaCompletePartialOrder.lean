import Mathlib.Order.OmegaCompletePartialOrder
import CoInd.Tactic
import CoInd.Kahn2

open OmegaCompletePartialOrder

-- define projections, map and lift operations over Pi types
namespace Pi

variable {α: Type u₁} {α': Type u₂}
variable {β: α → Type u₃} [(a : α) → OmegaCompletePartialOrder (β a)]
variable {γ: α → Type u₄} [(a : α) → OmegaCompletePartialOrder (γ a)]

@[simps! apply]
def OmegaCompletePartialOrder.proj (a: α) : ((a: α) → β a) →𝒄 (β a) where
  toFun p := p a
  monotone' := λ _ _ h₁ => h₁ a
  cont _ := rfl

@[simps! apply]
def OmegaCompletePartialOrder.map (f:(a: α) → β a →𝒄 γ a) : (∀ a, β a) →𝒄 (∀ a, γ a) where
  toFun p a := f a (p a)
  monotone' := λ x y h₁ a => (f a).monotone' (h₁ a)
  cont := by
    intro h c
    funext a
    apply (f a).cont
    apply (f a).monotone'

@[simps! apply]
def OmegaCompletePartialOrder.lift (f: α' → α) : (∀ a, β a) →𝒄 (∀ a, β (f a)) where
  toFun p a := p (f a)
  monotone' _ _ h₁ _ := h₁ _
  cont _ := rfl

example (f: α' → α) (p: ∀ a, β a) (a: α') :
  OmegaCompletePartialOrder.lift f p a = p (f a) := by
  simp

end Pi

@[simp]
def OmegaCompletePartialOrder.Fix.IterFun
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α → α) : ℕ → α
| n+1 => f (IterFun f n)
| 0 => ⊥

def OmegaCompletePartialOrder.Fix.IterFun_le_succ
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →o α) (n: ℕ) : IterFun f n ≤ IterFun f (n+1) := by
  induction n with
  | zero =>
    apply bot_le
  | succ n h₁ =>
    apply f.monotone'
    exact h₁

def OmegaCompletePartialOrder.Fix.IterFun_mono
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →o α) : Monotone (IterFun f) := by
  intro a b h₁
  induction h₁ with
  | refl =>
    apply le_refl
  | step _ h₂ =>
    apply h₂.trans
    apply IterFun_le_succ

@[simps! coe]
def OmegaCompletePartialOrder.Fix.Iter
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →o α) : Chain α where
  toFun := IterFun f
  monotone' := IterFun_mono f

def OmegaCompletePartialOrder.Fix
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →o α) : α := ωSup (Fix.Iter f)

-- fixed point of a continuous function
def OmegaCompletePartialOrder.FixCont
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →𝒄 α) : α := ωSup (Fix.Iter f)

namespace OmegaCompletePartialOrder.Fix
variable {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]

def unfold_mono (f: α →o α) : Fix f ≤ f (Fix f) := by
  apply ωSup_le
  intro n
  cases n with
  | zero =>
    apply bot_le
  | succ n =>
    apply f.monotone'
    apply le_ωSup (Iter f)

def unfold_cont (f: α →𝒄 α) : Fix f = f (Fix f) := by
  suffices Fix f = ωSup ((Iter f).map f.toOrderHom) by
    conv =>
      lhs
      rw [this, ←f.cont]
      rfl
  apply le_antisymm
  . apply ωSup_le
    intro n
    apply LE.le.trans _ (le_ωSup _ n)
    simp only [Chain.map_coe, Function.comp_apply]
    apply (Iter f.toOrderHom).monotone' (show n ≤ n+1 by simp)
  . apply ωSup_le
    intro n
    apply le_ωSup (Iter f.toOrderHom) (n+1)

end OmegaCompletePartialOrder.Fix



namespace OmegaCompletePartialOrder.Chain
variable {α: Type u} [OmegaCompletePartialOrder α]

def filter (c: Chain α) (U: ℕ →o ℕ) : Chain α := c.comp U

-- ensure that an increasing seauence `c` filtred by `U` have a supremum less than
-- the supremum of `c`
def ωSup_filter (c: Chain α) (U: ℕ →o ℕ) : ωSup (filter c U) ≤ ωSup c := by
  apply ωSup_le
  intro n
  apply le_ωSup c (U n)

-- ensure that if an increasing sequance `c` is filtred with an injective function `U`, then
-- the supremum of `c` and `c.filter u` are equals
def ωSup_filter_inj (c: Chain α) (U: ℕ →o ℕ) (inj: Function.Injective U) : ωSup (c.filter U) = ωSup c := by
  apply le_antisymm
  . apply ωSup_filter
  . apply ωSup_le
    intro n
    have : ∀ n, n ≤ U n := by
      intro n
      induction n with
      | zero =>
        apply Nat.zero_le
      | succ n h =>
        have := Nat.succ_le_succ h
        apply this.trans
        have := @Nat.lt_iff_le_and_ne (U n) (U (.succ n))
        apply this.mpr
        constructor
        . apply U.monotone
          simp_arith
        . intro h
          specialize inj h
          cases inj
    apply le_trans _ (le_ωSup (filter c U) n)
    apply c.monotone'
    apply this

end OmegaCompletePartialOrder.Chain

def OmegaCompletePartialOrder.IsAdmissible {α: Type u} [OmegaCompletePartialOrder α] (S: Set α) :=
  ∀ (c: Chain α), (∀ n, S (c n)) → S (ωSup c)

structure OmegaCompletePartialOrder.Admissible
  (α: Type u) [OmegaCompletePartialOrder α] [OrderBot α] where
  toSet : Set α
  admissible': IsAdmissible toSet
  contain_bot: ⊥ ∈ toSet

attribute [coe] Admissible.toSet

namespace OmegaCompletePartialOrder.Admissible
variable {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]

instance instFunLike : FunLike (Admissible α) α (λ _ => Prop) where
  coe := toSet
  coe_injective' := by
    intro a b h₁
    cases a
    cases b
    rw [Admissible.mk.injEq]
    exact h₁

instance : CoeFun (Admissible α) fun _ => α → Prop := ⟨toSet⟩

instance : Membership α (Admissible α) :=
  ⟨λ x s => s x⟩

@[refinment_type] def admissible (p: Admissible α) (c: Chain α) :
  (∀ n, c n ∈ p) → ωSup c ∈ p := p.admissible' c

-- Conjunction of two properties
def And (lhs rhs: Admissible α) : Admissible α where
  toSet x := x ∈ lhs ∧ x ∈ rhs

  admissible' := by
    intro c h₁
    constructor
    . apply lhs.admissible'
      intro n
      specialize h₁ n
      exact h₁.left
    . apply rhs.admissible'
      intro n
      specialize h₁ n
      exact h₁.right

  contain_bot := by
    constructor
    . exact lhs.contain_bot
    . exact rhs.contain_bot

@[refinment_type] def And.intro (lhs rhs: Admissible α) (x: α) :
  x ∈ lhs → x ∈ rhs → x ∈ And lhs rhs := by
  intro a v
  constructor
  <;> assumption

def Or.prop (p: Admissible α) (c: Chain α) (n: Nat) (m: Nat) : Prop := p (c (n+m))

/-
Define an increasing and injective sequence such that if `p` hold infinitly many times
in `c`, then `p` hold for each elements of `sequence p c`
-/
noncomputable def Or.sequence (p: Admissible α) (c: Chain α) : Nat → Nat
| n+1 =>
  let m := sequence p c n
  (m+1) + Classical.epsilon (prop p c (m + 1))
| 0 => Classical.epsilon (prop p c 0)

theorem Or.sequence.strict_mono' (p: Admissible α) (c: Chain α) (n: ℕ) :
  sequence p c n < sequence p c (n+1) := by
  rw [sequence]
  simp_arith

theorem Or.sequence.strict_mono (p: Admissible α) (c: Chain α) (n m: ℕ) (h₁: n < m) :
  sequence p c n < sequence p c m := by
  induction h₁ with
  | refl =>
    apply strict_mono'
  | step _ h₂ =>
    apply h₂.trans
    apply strict_mono'

theorem Or.sequence.inj (p: Admissible α) (c: Chain α) : Function.Injective (sequence p c) := by
  intro a b h₁
  cases Nat.le_or_le a b with
  | inl h₂ =>
    cases le_iff_lt_or_eq.mp h₂ with
    | inl h₃ =>
      have := strict_mono p c a b h₃
      rw [h₁] at this
      simp at this
    | inr h₃ =>
      assumption
  | inr h₂ =>
    cases le_iff_lt_or_eq.mp h₂ with
    | inl h₃ =>
      have := strict_mono p c b a h₃
      rw [h₁] at this
      simp at this
    | inr h₃ =>
      cases h₃
      rfl

noncomputable def Or.sequence' (p: Admissible α) (c: Chain α) : ℕ →o ℕ where
  toFun := sequence p c
  monotone' := by
    intro a b h₁
    induction h₁ with
    | refl =>
      apply le_refl
    | step _ h₂ =>
      apply h₂.trans
      simp_arith [sequence]

def Or.sequence_spec (p: Admissible α) (c: Chain α) :
  (∀ n, ∃ m, p (c (n + m))) → ∀ n, p (c.filter (Or.sequence' p c) n) := by
  intro h₁ n
  cases n with
  | zero =>
    simp [Chain.filter, sequence', sequence, prop]
    apply @Classical.epsilon_spec _ (λ m => p (c m))
    specialize h₁ 0
    conv at h₁ =>
      rhs; intro m
      rw [Nat.zero_add]
      rfl
    assumption
  | succ m =>
    simp [Chain.filter, sequence', sequence, prop]
    apply @Classical.epsilon_spec _ (λ m' => p <| c <| sequence p c m + 1 + m')
    apply h₁

def Or.pigeonhole (p q: Admissible α) (c: Chain α) (h₁: ∀ n, p (c n) ∨ q (c n)) :
  (∀ n, ∃ m, p (c (n+m))) ∨ (∀ n, ∃ m, q (c (n+m))) := by
  by_cases (∀ n, ∃ m, p (c (n+m)))
  . apply Or.inl h
  . apply Or.inr
    intro n
    conv at h =>
      rw [not_forall]
      rhs; intro k
      rw [not_exists]
      rfl
    have ⟨k, h⟩ := h
    specialize h n
    rw [add_comm] at h
    specialize h₁ (n+k)
    exists k
    simp only [h, false_or] at h₁
    assumption

/- Disjunction of two admissible properties -/
def Or (lhs rhs: Admissible α) : Admissible α where
  toSet x := x ∈ lhs ∨ x ∈ rhs

  contain_bot := by
    apply Or.inl
    exact lhs.contain_bot

  admissible' := by
    intro c h₁

    let lhsS := Or.sequence' lhs c
    let rhsS := Or.sequence' rhs c
    let lhsC := c.filter lhsS
    let rhsC := c.filter rhsS
    have lhsI : ωSup lhsC = ωSup c := Chain.ωSup_filter_inj c lhsS (Or.sequence.inj _ _)
    have rhsI : ωSup rhsC = ωSup c := Chain.ωSup_filter_inj c rhsS (Or.sequence.inj _ _)
    conv =>
      congr
      . rw [←lhsI]
      . rw [←rhsI]
    cases Or.pigeonhole lhs rhs c h₁ with
    | inl h₂ =>
      apply Or.inl
      apply lhs.admissible'
      apply Or.sequence_spec lhs c h₂
    | inr h₂ =>
      apply Or.inr
      apply rhs.admissible'
      apply Or.sequence_spec rhs c h₂


def Forall {β: Type v} (p: β → Admissible α) : Admissible α where
  toSet x := ∀ y, x ∈ p y
  contain_bot := by
    intro y
    apply (p y).contain_bot
  admissible' := by
    intro c h₁ y
    apply (p y).admissible'
    intro n
    apply h₁

@[refinment_type] def contain_bot' (p: Admissible α) : ⊥ ∈ p := p.contain_bot

-- If a proposition `p` is admissible then if is enough to show that `p` is stable
-- by `f` to show that `Fix f` ensure `p`
@[refinment_type] def Fix_thm (p: Admissible α) (f: α →o α) (hyp: ∀ x, x ∈ p → f x ∈ p) : Fix f ∈ p := by
  apply p.admissible' (Fix.Iter f)
  intro n
  induction n with
  | zero =>
    apply p.contain_bot
  | succ n h₁ =>
    exact hyp (Fix.Iter f n) h₁


end OmegaCompletePartialOrder.Admissible
