import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.Linarith
import CoInd.Tactic
import CoInd.Kahn
import CoInd.OmegaCompletePartialOrder

open OmegaCompletePartialOrder

-- As admissible functions are just continuous functions to Prop, it is possible to define the composition of
-- continuous functions and admissible properties. Then one can define an admissible invariant over a lustre
-- node as the composition of Square and an admissible function from the state of the node to Kahn Prop
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
def Square.cons (x: Prop) (xs: Kahn Prop) :
  x → Square xs → Square (x ::: xs) := by
  intro h₁ h₂
  simp only [Square, Membership.mem]
  rw [←pgfp.unfold]
  apply Square.SetF.cons x xs rfl h₁ (Or.inr h₂)

@[simp]
def Square.rewrite_cons (x: Prop) (xs: Kahn Prop) :
  Square (x ::: xs) = (x ∧ Square xs) := by
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
def Square.bot :
  Square ⊥ := by
  simp only [Square]
  rw [←pgfp.unfold]
  apply Square.SetF.bot rfl

def Square.coind (hyp: Kahn Prop → Prop) :
  (∀ x, hyp x → Square.SetF (λ x => hyp x ∨ Square x) x)
  → ∀ x, hyp x → Square x := by
  intro h₁ x h₂
  simp only [Membership.mem, Square]
  apply pgfp.theorem _ hyp
  clear h₂ x
  intro x h₂
  specialize h₁ x h₂
  have : (fun x => hyp x ∨ Square x) ≤ hyp ⊔ (pgfp SetF_mono) hyp := by
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

def Square.and
  [OmegaCompletePartialOrder α] [OrderBot α]
  (P Q: α →𝒄 Kahn Prop) (x: α) (h: Admissible.And (Square.comp P) (Square.comp Q) x) :
  Square ((P x).and (Q x)) := by
  simp [Admissible.And] at h
  coinduction [h] generalizing [P x, Q x] using Square.coind
  intro pqx ⟨px, qx, eq₁, h₁, h₂⟩
  induction eq₁
  cases px with
  | bot =>
    apply SetF.bot
    simp
  | cons px pxs =>
    cases qx with
    | bot =>
      apply SetF.bot
      simp
    | cons qx qxs =>
      simp only [rewrite_cons] at h₁ h₂
      apply SetF.cons (px ∧ qx) (pxs.and qxs)
      · simp
      · exact ⟨h₁.left, h₂.left⟩
      · apply Or.inl
        exists pxs
        exists qxs
        simp only [true_and]
        exact ⟨h₁.right, h₂.right⟩

def Square.or
  [OmegaCompletePartialOrder α] [OrderBot α]
  (P Q: α →𝒄 Kahn Prop) (x: α) (h: Admissible.Or (Square.comp P) (Square.comp Q) x) :
  Square ((P x).or (Q x)) := by
  simp [Admissible.Or] at h
  coinduction [h] generalizing [P x, Q x] using Square.coind
  rintro pqx ⟨px, qx, eq₁, (h₁ | h₁)⟩
  <;> induction eq₁
  · cases px with
    | bot =>
      apply SetF.bot
      simp
    | cons px pxs =>
      cases qx with
      | bot =>
        apply SetF.bot
        simp
      | cons qx qxs =>
        simp at h₁
        apply SetF.cons px (pxs.or qxs) _ h₁.left
        · apply Or.inl
          exists pxs
          exists qxs
          simp [h₁.right]
        · simp [h₁.left]
  · cases px with
    | bot =>
      apply SetF.bot
      simp
    | cons px pxs =>
      cases qx with
      | bot =>
        apply SetF.bot
        simp
      | cons qx qxs =>
        simp at h₁
        apply SetF.cons qx (pxs.or qxs) _ h₁.left
        · apply Or.inl
          exists pxs
          exists qxs
          simp [h₁.right]
        · simp [h₁.left]



--def Square.coind3
--  [OmegaCompletePartialOrder α] [OrderBot α]
--  (f: α →𝒄 α) (prop: α →𝒄 Kahn Prop) (hyp: α → Prop)
--  (h₀: ∀ x y ys, Square (prop x) → prop x = y ::: ys → y ∧ Square ys)
--  : Square (prop x) := by

def Square.coind2
  [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →𝒄 Kahn Prop) (hyp: α → Prop) :
  (∀ x, hyp x → f x = ⊥ ∨ ∃ y ys, f x = y ::: xs ∧ y ∧ hyp ys)
  → ∀ x, hyp x → Square (f x) := by
  intro h₁ x h₂
  coinduction generalizing [x, f x] using Square.coind
  intro w ⟨x, fx, eq₁, h₁, h₂⟩
  induction eq₁
  specialize h₁ x h₂
  sorry





syntax:max "□" term:max : term
macro_rules
| `(□ $t) => `(Square $t)


delab_rule Square
| `($_ $P) => do ``(□ $P)

end Kahn
