import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.Linarith
import CoInd.Tactic
import CoInd.Kahn
import CoInd.OmegaCompletePartialOrder

open OmegaCompletePartialOrder

-- As admissible functions are just continuous functions to Prop,
-- it is possible to define the composition of continuous functions
-- and admissible properties. Then one can define an admissible
-- invariant over a lustre node as the composition of Box and an
-- admissible function from the state of the node to Kahn Prop
def OmegaCompletePartialOrder.Admissible.comp {α: Type u} {β: Type v}
  [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [OrderBot α] [OrderBot β]
  (p: Admissible β) (f: α →𝒄 β) : Admissible α where
  toSet x := p (f x)
  admissible' := by
    intro chain h₁
    rw [f.continuous]
    apply p.admissible
    exact h₁

@[simp] def OmegaCompletePartialOrder.Admissible.comp_apply {α: Type u} {β: Type v}
  [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [OrderBot α] [OrderBot β]
  (p: Admissible β) (f: α →𝒄 β) (x: α) : (comp p f x) = (p (f x)) := by
  rfl

namespace Kahn
inductive Box.SetF
  (aux: Set (Kahn Prop)) (s: Kahn Prop) : Prop where
| bot : ⊥ = s → SetF aux s
| cons x xs : x ::: xs = s → x → aux xs → SetF aux s

@[simps! coe]
def Box.SetF_mono : (Kahn Prop → Prop) →o (Kahn Prop → Prop) where
  toFun aux x := Box.SetF aux x
  monotone' s₁ s₂ h₁ x h₂ := by
    cases x using Kahn.cases with
    | bot =>
      apply SetF.bot
      rfl
    | cons x xs =>
      apply SetF.cons x xs
      · rfl
      · cases h₂ with
        | bot h₃ =>
          simp [Bot.bot, Kahn.cons] at h₃
        | cons y ys h₃ h₄ h₅ =>
          rw [Kahn.cons.injEq] at h₃
          induction h₃.left
          induction h₃.right
          assumption
      · cases h₂ with
        | bot h₃ =>
          simp [Bot.bot, Kahn.cons] at h₃
        | cons y ys h₃ h₄ h₅ =>
          rw [Kahn.cons.injEq] at h₃
          induction h₃.left
          induction h₃.right
          apply h₁
          assumption


noncomputable def Box : Admissible (Kahn Prop) where
  toSet s := pgfp (Box.SetF_mono) ⊥ s

  admissible' := by
    intro chain h₁
    coinduction [h₁] generalizing [chain] using pgfp.theorem Box.SetF_mono
    intro _ ⟨chain, eq₁, h₁⟩
    induction eq₁
    rw [Kahn.ωSup.unfold]
    cases Kahn.findCons chain with
    | bot h₂ =>
      apply Box.SetF.bot
      rfl
    | cons n x xs h₂ =>
      apply Box.SetF.cons x (ωSup xs)
      · rfl
      · specialize h₁ (n+0)
        rw [←h₂ 0, ←pgfp.unfold] at h₁
        cases h₁ with
        | bot h₃ =>
          simp [Bot.bot, Kahn.cons] at h₃
        | cons y ys h₃ h₄ h₅ =>
          rw [Kahn.cons.injEq] at h₃
          induction h₃.left
          assumption
      · apply Or.inl
        exists xs
        constructor
        · rfl
        · intro m
          specialize h₁ (n+m)
          rw [←h₂ m, ←pgfp.unfold] at h₁
          cases h₁ with
          | bot h₃ =>
            simp [Bot.bot, Kahn.cons] at h₃
          | cons y ys h₃ h₄ h₅ =>
            rw [Kahn.cons.injEq] at h₃
            induction h₃.left
            induction Eq.symm h₃.right
            cases h₅ with
            | inl h =>
              cases h
            | inr h =>
              exact h

#check pgfp.unfold

@[refinment_type]
def Box.cons (x: Prop) (xs: Kahn Prop) :
  x → Box xs → Box (x ::: xs) := by
  intro h₁ h₂
  simp only [Box, Membership.mem]
  rw [←pgfp.unfold]
  apply Box.SetF.cons x xs rfl h₁ (Or.inr h₂)

@[simp]
def Box.rewrite_cons (x: Prop) (xs: Kahn Prop) :
  Box (x ::: xs) = (x ∧ Box xs) := by
  apply propext
  constructor
  · intro h
    simp only [Box, Membership.mem] at h
    rw [←pgfp.unfold] at h
    cases h with
    | bot eq =>
      simp [Bot.bot, Kahn.cons] at eq
    | cons y ys eq h₁ h₂ =>
      rw [Kahn.cons.injEq] at eq
      induction eq.left
      induction eq.right
      constructor
      · exact h₁
      · cases h₂ with
        | inl h =>
          cases h
        | inr h =>
          exact h
  · intro ⟨h₁, h₂⟩
    refinment_type

@[refinment_type]
def Box.bot :
  Box ⊥ := by
  simp only [Box]
  rw [←pgfp.unfold]
  apply Box.SetF.bot rfl

def Box.coind (hyp: Kahn Prop → Prop) :
  (∀ x, hyp x → Box.SetF (λ x => hyp x ∨ Box x) x)
  → ∀ x, hyp x → Box x := by
  intro h₁ x h₂
  simp only [Membership.mem, Box]
  apply pgfp.theorem _ hyp
  clear h₂ x
  intro x h₂
  specialize h₁ x h₂
  have : (fun x => hyp x ∨ Box x) ≤ hyp ⊔ (pgfp SetF_mono) hyp := by
    intro x h₁
    cases h₁ with
    | inl h => apply Or.inl h
    | inr h =>
      apply Or.inr
      apply (pgfp SetF_mono).monotone (OrderBot.bot_le _)
      exact h
  apply SetF_mono.monotone this
  apply h₁
  apply h₂

-- Box P ∧ Box Q → Box (P.and Q) but the inverse is false because we
-- must ensure that the streams are not finite. In practice we prefere
-- (Box P).Admissible (Box Q) instead of Box (P.and Q)
def Box.and
  [OmegaCompletePartialOrder α] [OrderBot α]
  (P Q: Kahn Prop)
  (h: Box P ∧ Box Q) :
  Box (P.and Q) := by
  coinduction [h] generalizing [P, Q] using Box.coind
  intro pq ⟨p, q, eq₁, h₁, h₂⟩
  induction eq₁
  cases p with
  | bot =>
    apply SetF.bot
    simp
  | cons p ps =>
    cases q with
    | bot =>
      apply SetF.bot
      simp
    | cons q qs =>
      simp only [rewrite_cons] at h₁ h₂
      apply SetF.cons (p ∧ q) (ps.and qs)
      · simp
      · exact ⟨h₁.left, h₂.left⟩
      · apply Or.inl
        exists ps
        exists qs
        simp only [true_and]
        exact ⟨h₁.right, h₂.right⟩

-- Same as Kahn.and, Kahn.or is very limited because we must ensure that streams
-- are infinite to use it. In practice we prefere
-- (Box P).Admissible (Box Q) instead of Box (P.or Q)
def Box.or
  [OmegaCompletePartialOrder α] [OrderBot α]
  (P Q: Kahn Prop) (h: Box P ∨ Box Q) :
  Box (P.or Q) := by
  coinduction [h] generalizing [P, Q] using Box.coind
  rintro pq ⟨p, q, eq₁, (h₁ | h₁)⟩
  <;> induction eq₁
  · cases p with
    | bot =>
      apply SetF.bot
      simp
    | cons p ps =>
      cases q with
      | bot =>
        apply SetF.bot
        simp
      | cons q qs =>
        simp at h₁
        apply SetF.cons p (ps.or qs) _ h₁.left
        · apply Or.inl
          exists ps
          exists qs
          simp [h₁.right]
        · simp [h₁.left]
  · cases p with
    | bot =>
      apply SetF.bot
      simp
    | cons p ps =>
      cases q with
      | bot =>
        apply SetF.bot
        simp
      | cons q qs =>
        simp at h₁
        apply SetF.cons q (ps.or qs) _ h₁.left
        · apply Or.inl
          exists ps
          exists qs
          simp [h₁.right]
        · simp [h₁.left]



def Box.coind2
  [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →𝒄 Kahn Prop) (hyp: α → Prop) :
  (∀ x, hyp x → f x = ⊥ ∨ ∃ y ys, f x = y ::: xs ∧ y ∧ hyp ys)
  → ∀ x, hyp x → Box (f x) := by
  intro h₁ x h₂
  coinduction generalizing [x, f x] using Box.coind
  intro w ⟨x, fx, eq₁, h₁, h₂⟩
  induction eq₁
  specialize h₁ x h₂
  sorry

end Kahn

syntax:max "□" term:max : term
macro_rules
| `(□ $t) => `(Kahn.Box $t)

-- I try to pretty-print Kahn.Box using □ but I fail because of the implicit
-- coercions...
--delab_rule Kahn.Box
--| `($_ $P) => do ``(□ $P)
