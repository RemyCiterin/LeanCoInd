import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.Linarith
import CoInd.Tactic
import CoInd.Kahn
import CoInd.OmegaCompletePartialOrder
import CoInd.Lustre

open OmegaCompletePartialOrder

-- As admissible functions are just continuous functions to Prop, it is possible to define the composition of
-- continuous functions and admissible properties. Then one can define an admissible invariant over a lustre
-- node as the composition of Square and an admissible function from the state of the node to Kahn Prop
def Admissible.comp {α: Type u} {β: Type v}
  [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [OrderBot α] [OrderBot β]
  (p: Admissible β) (f: α →𝒄 β) : Admissible α where
  toSet x := f x ∈ p
  admissible' := by
    intro chain h₁
    rw [f.continuous]
    apply p.admissible
    exact h₁

inductive Square.SetF
  (aux: Set (Kahn Prop)) (s: Kahn Prop) : Prop where
| bot : ⊥ = s → SetF aux s
| cons x xs : x ::: xs = s → x → aux xs → SetF aux s

@[simps! coe]
def Square.SetF_mono : (Kahn Prop → Prop) →o (Kahn Prop → Prop) where
  toFun aux x := Square.SetF aux x
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


noncomputable def Square : Admissible (Kahn Prop) where
  toSet s := pgfp (Square.SetF_mono) ⊥ s

  admissible' := by
    intro chain h₁
    coinduction [h₁] generalizing [chain] using pgfp.theorem Square.SetF_mono
    clear h₁ chain
    intro _ ⟨chain, eq₁, h₁⟩
    induction eq₁
    rw [Kahn.ωSup.unfold]
    cases Kahn.findCons chain with
    | bot h₂ =>
      apply Square.SetF.bot
      rfl
    | cons n x xs h₂ =>
      apply Square.SetF.cons x (ωSup xs)
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
def Square.unfold_cons (x: Prop) (xs: Kahn Prop) :
  x → xs ∈ Square → x ::: xs ∈ Square := by
  intro h₁ h₂
  simp only [Square, Membership.mem]
  rw [←pgfp.unfold]
  apply Square.SetF.cons x xs rfl h₁ (Or.inr h₂)

@[simp]
def Square.rewrite_cons (x: Prop) (xs: Kahn Prop) :
  (x ::: xs ∈ Square) = (x ∧ xs ∈ Square) := by
  apply propext
  constructor
  · intro h
    simp only [Square, Membership.mem] at h
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
def Square.unfold_bot :
  ⊥  ∈ Square := by
  simp only [Square, Membership.mem]
  rw [←pgfp.unfold]
  apply Square.SetF.bot rfl

def Square.coind (hyp: Kahn Prop → Prop) :
  (∀ x, hyp x → Square.SetF (λ x => hyp x ∨ x ∈ Square) x)
  → ∀ x, hyp x → x ∈ Square := by
  intro h₁ x h₂
  simp only [Membership.mem, Square]
  apply pgfp.theorem _ hyp
  clear h₂ x
  intro x h₂
  specialize h₁ x h₂
  have : (fun x => hyp x ∨ x ∈ Square) ≤ hyp ⊔ (pgfp SetF_mono) hyp := by
    intro x h₁
    cases h₁ with
    | inl h => apply Or.inl h
    | inr h =>
      apply Or.inr
      apply (pgfp SetF_mono).monotone bot_le
      exact h
  apply SetF_mono.monotone this
  apply h₁
  apply h₂
