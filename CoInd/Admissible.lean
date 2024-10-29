import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.Linarith
import CoInd.Tactic
import CoInd.Kahn
import CoInd.OmegaCompletePartialOrder

import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq


open Lean Lean.Macro

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

namespace ωStream
inductive Box.SetF
  (aux: Set (ωStream Prop)) (s: ωStream Prop) : Prop where
| bot : ⊥ = s → SetF aux s
| cons x xs : x ::: xs = s → x → aux xs → SetF aux s

@[simps! coe]
def Box.SetF_mono : (ωStream Prop → Prop) →o (ωStream Prop → Prop) where
  toFun aux x := Box.SetF aux x
  monotone' s₁ s₂ h₁ x h₂ := by
    cases x using ωStream.cases with
    | bot =>
      apply SetF.bot
      rfl
    | cons x xs =>
      apply SetF.cons x xs
      · rfl
      · cases h₂ with
        | bot h₃ =>
          simp [Bot.bot, Cons.cons] at h₃
        | cons y ys h₃ h₄ h₅ =>
          rw [ωStream.cons.injEq] at h₃
          induction h₃.left
          induction h₃.right
          assumption
      · cases h₂ with
        | bot h₃ =>
          simp [Bot.bot, Cons.cons] at h₃
        | cons y ys h₃ h₄ h₅ =>
          rw [ωStream.cons.injEq] at h₃
          induction h₃.left
          induction h₃.right
          apply h₁
          assumption


noncomputable def Box : Admissible (ωStream Prop) where
  toSet s := pgfp (Box.SetF_mono) ⊥ s

  admissible' := by
    intro chain h₁
    coinduction [h₁] generalizing [chain] using pgfp.theorem Box.SetF_mono
    intro _ ⟨chain, eq₁, h₁⟩
    induction eq₁
    rw [ωStream.ωSup.unfold]
    cases ωStream.findCons chain with
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
          simp [Bot.bot, Cons.cons] at h₃
        | cons y ys h₃ h₄ h₅ =>
          rw [ωStream.cons.injEq] at h₃
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
            simp [Bot.bot, Cons.cons] at h₃
          | cons y ys h₃ h₄ h₅ =>
            rw [ωStream.cons.injEq] at h₃
            induction h₃.left
            induction Eq.symm h₃.right
            cases h₅ with
            | inl h =>
              cases h
            | inr h =>
              exact h

#check pgfp.unfold

@[refinment_type]
def Box.cons (x: Prop) (xs: ωStream Prop) :
  x → Box xs → Box (x ::: xs) := by
  intro h₁ h₂
  simp only [Box, Membership.mem]
  rw [←pgfp.unfold]
  apply Box.SetF.cons x xs rfl h₁ (Or.inr h₂)

@[simp]
def Box.rewrite_cons (x: Prop) (xs: ωStream Prop) :
  Box (x ::: xs) = (x ∧ Box xs) := by
  apply propext
  constructor
  · intro h
    simp only [Box, Membership.mem] at h
    rw [←pgfp.unfold] at h
    cases h with
    | bot eq =>
      simp [Bot.bot, Cons.cons] at eq
    | cons y ys eq h₁ h₂ =>
      rw [ωStream.cons.injEq] at eq
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

def Box.coind (hyp: ωStream Prop → Prop) :
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
  (P Q: ωStream Prop)
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

-- Same as Kahn.and, ωStream.or is very limited because we must ensure that streams
-- are infinite to use it. In practice we prefere
-- (Box P).Admissible (Box Q) instead of Box (P.or Q)
def Box.or
  [OmegaCompletePartialOrder α] [OrderBot α]
  (P Q: ωStream Prop) (h: Box P ∨ Box Q) :
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



--def Box.coind2
--  [OmegaCompletePartialOrder α] [OrderBot α]
--  (f: α →𝒄 ωStream Prop) (hyp: α → Prop) :
--  (∀ x, hyp x → f x = ⊥ ∨ ∃ y ys, f x = y ::: xs ∧ y ∧ hyp ys)
--  → ∀ x, hyp x → Box (f x) := by
--  intro h₁ x h₂
--  coinduction generalizing [x, f x] using Box.coind
--  intro w ⟨x, fx, eq₁, h₁, h₂⟩
--  induction eq₁
--  specialize h₁ x h₂
--  sorry

end ωStream

syntax:max "□" term:max : term
macro_rules
| `(□ $t) => `(ωStream.Box $t)

-- I try to pretty-print ωStream.Box using □ but I fail because of the implicit
-- coercions...
--delab_rule ωStream.Box
--| `($_ $P) => do ``(□ $P)

inductive ωStream.Entails.F (aux: ωStream Prop → ωStream Prop → Prop)
  (s₁: ωStream Prop) (s₂: ωStream Prop) : Prop where
| bot_left :
  ⊥ = s₁ → F aux s₁ s₂
| bot_right :
  ⊥ = s₂ → F aux s₁ s₂
| cons (x y: Prop) (xs ys: ωStream Prop) :
  (x → y) → aux xs ys →
  x ::: xs = s₁ → y ::: ys = s₂ →
  F aux s₁ s₂

@[refinment_type]
def ωStream.Entails.F.Cons
  (r: ωStream Prop → ωStream Prop → Prop)
  (p q: Prop) (ps qs : ωStream Prop) :
  (p → q) → r ps qs → F r (p ::: ps) (q ::: qs) :=
  λ h₁ h₂ => cons p q ps qs h₁ h₂ rfl rfl

@[refinment_type]
def ωStream.Entails.F.BotLeft
  (r: ωStream Prop → ωStream Prop → Prop)
  (q: ωStream Prop) : F r ⊥ q  :=
  bot_left rfl

@[refinment_type]
def ωStream.Entails.F.BotRight
  (r: ωStream Prop → ωStream Prop → Prop)
  (p: ωStream Prop) : F r p ⊥  :=
  bot_right rfl

def ωStream.Entails.F.mono :
  (ωStream Prop → ωStream Prop → Prop) →o
  (ωStream Prop → ωStream Prop → Prop) where
  toFun := F
  monotone' := by
    intro r₁ r₂ h₁ s₁ s₂ h₂
    cases h₂ with
    | bot_left h₂ =>
      induction h₂
      refinment_type
    | bot_right h₂ =>
      induction h₂
      refinment_type
    | cons x y xs ys h₂ h₃ h₄ h₅ =>
      induction h₄
      induction h₅
      refinment_type
      apply h₁
      assumption

def ωStream.Entails : ωStream Prop → ωStream Prop → Prop :=
  pgfp Entails.F.mono ⊥


def ωStream.Entails.unfold (s₁ s₂: ωStream Prop) :
  Entails s₁ s₂ ↔ F Entails s₁ s₂ := by
  constructor
  <;> intro h₁
  · rw [Entails, ←pgfp.unfold] at h₁
    cases h₁
    case bot_left h₁ =>
      apply F.bot_left h₁
    case bot_right h₁ =>
      apply F.bot_right h₁
    case cons x y xs ys h₁ h₂ eq₁ eq₂ =>
      simp only [Pi.sup_apply, Pi.bot_apply, Prop.bot_eq_false,
        le_Prop_eq, false_implies, sup_of_le_right] at h₂
      apply F.cons x y xs ys h₁ h₂ eq₁ eq₂
  · rw [Entails, ←pgfp.unfold]
    cases h₁
    case bot_left h₁ =>
      apply F.bot_left h₁
    case bot_right h₁ =>
      apply F.bot_right h₁
    case cons x y xs ys h₁ h₂ eq₁ eq₂ =>
      apply F.cons x y xs ys h₁ (Or.inr h₂) eq₁ eq₂


def ωStream.Entails.cons (x y: Prop) (xs ys: ωStream Prop)
  (h₁: x → y) (h₂: Entails xs ys) : Entails (x ::: xs) (y ::: ys) := by
  rw [Entails, ←pgfp.unfold]
  apply F.cons x y xs ys h₁ (Or.inr h₂) rfl rfl

@[simp] def ωStream.Entails.consEq (x y: Prop) (xs ys: ωStream Prop) :
  Entails (x ::: xs) (y ::: ys) = ((x → y) ∧ Entails xs ys) := by
  apply propext
  constructor
  · intro h₁
    rw [Entails, ←pgfp.unfold] at h₁
    cases h₁ with
    | bot_left h₁ =>
      simp [Cons.cons, Bot.bot] at h₁
    | bot_right h₁ =>
      simp [Cons.cons, Bot.bot] at h₁
    | cons a b as bs h₁ h₂ h₃ h₄ =>
      rw [ωStream.cons.injEq] at h₃ h₄
      induction h₃.1
      induction h₃.2
      induction h₄.1
      induction h₄.2
      constructor
      · assumption
      · cases h₂ with
        | inl h₂ =>
          cases h₂
        | inr h₂ =>
          exact h₂
  · intro h₁
    apply Entails.cons _ _ _ _ h₁.1 h₁.2

def ωStream.Entails.bot_left (y: ωStream Prop)
  : Entails ⊥ y := by
  rw [Entails, ←pgfp.unfold]
  apply F.bot_left rfl

def ωStream.Entails.bot_right (x: ωStream Prop)
  : Entails x ⊥ := by
  rw [Entails, ←pgfp.unfold]
  apply F.bot_right rfl

#check pgfp.unfold
#check pgfp.accumulate

def ωStream.Entails.coind (hyp: ωStream Prop → ωStream Prop → Prop)
  (h₁: ∀ s₁ s₂, hyp s₁ s₂ → F hyp s₁ s₂)
  (s₁ s₂: ωStream Prop) (h₂: hyp s₁ s₂) :
  Entails s₁ s₂ := by
  have := (pgfp.accumulate F.mono ⊥ hyp).2
  simp only [_root_.bot_le, sup_of_le_right] at this
  specialize this _ s₁ s₂
  · intro s₁ s₂ h₂
    rw [←pgfp.unfold]
    cases h₁ _ _ h₂
    case bot_left h =>
      apply F.bot_left h
    case bot_right h =>
      apply F.bot_right h
    case cons x y xs ys h₁ h₂ eq₁ eq₂ =>
      apply F.cons x y xs ys
      · apply h₁
      · apply Or.inl h₂
      · apply eq₁
      · apply eq₂
  · specialize this h₂
    exact this

#check ωStream.ωSup_cons

-- A proof that (Entails P) is admissible for all P, in particular P may
-- represent the precondition of a lustre node
def ωStream.Entails.admissible (P: ωStream Prop) : IsAdmissible (Entails P) :=
by
  intro chain h₁
  coinduction generalizing [chain, P] using coind
  intro l r ⟨chain, P, eq₁, eq₂, h₁⟩
  induction eq₁
  induction eq₂
  cases findCons chain with
  | bot h₂ =>
    rw [ωSup_bot]
    · refinment_type
    · assumption
  | cons n Q₀ Q h₂ =>
    cases P with
    | bot =>
      refinment_type
    | cons P₀ P =>
      rw [ωSup_cons _ n Q₀ Q h₂]
      refinment_type
      · specialize h₁ (n + 0)
        rw [←h₂ 0] at h₁
        simp only [consEq] at h₁
        exact h₁.left
      · exists Q
        simp only [true_and, exists_eq_left]
        intro k
        specialize h₁ (n+k)
        rw [←h₂ k] at h₁
        simp only [consEq] at h₁
        apply h₁.right

def ωStream.imp (P Q: ωStream Prop) : ωStream Prop :=
  P.not.or Q

def ωStream.imp.unfold_bot_left (Q: ωStream Prop) :
  ωStream.imp ⊥ Q = ⊥ := by
  simp [imp]

def ωStream.imp.unfold_bot_right (P: ωStream Prop) :
  ωStream.imp P ⊥ = ⊥ := by
  simp [imp]

def ωStream.imp.unfold_cons (P Q: Prop) (Ps Qs: ωStream Prop) :
  (P ::: Ps).imp (Q ::: Qs) = (P → Q) ::: Ps.imp Qs := by
  simp only [imp, or.unfold_cons, not.unfold_cons]
  rw [ωStream.cons.injEq]
  simp only [and_true, eq_iff_iff]
  constructor
  · rintro (h|h) h'
    · cases h h'
    · assumption
  · intro h
    by_cases P
    case pos h' =>
      exact (Or.inr (h h'))
    case neg h' =>
      exact (Or.inl h')

def OmegaCompletePartialOrder.ContinuousHom.ωStream.imp :
  ωStream Prop × ωStream Prop →𝒄 ωStream Prop :=
  ωStream.or.comp <| Prod.prod
    (ωStream.not.comp Prod.fst)
    Prod.snd

def OmegaCompletePartialOrder.ContinuousHom.ωStream.imp_apply
  (P Q: ωStream Prop) : ωStream.imp (P, Q) = _root_.ωStream.imp P Q :=
  rfl

-- Duplicate is not a monotone function because
--     x ::: ⊥ ≤ x ::: y ::: ⊥
-- but
--     duplicate (x ::: ⊥) = (x ::: ⊥) ::: ⊥
-- and
--     duplicate (x ::: y ::: ⊥) = (x ::: y ::: ⊥) ::: (y ::: ⊥) ::: ⊥
-- so
--     duplicate (x ::: ⊥) ≰ duplicate (x ::: y ::: ⊥)
def ωStream.duplicate : ωStream α → ωStream (ωStream α) :=
  corec (λ x =>
    ωStream.cases x
      (cons := λ x xs => F.cons (x ::: xs) xs)
      (bot := F.bot)
  )

@[simp] def ωStream.duplicate.unfold_bot :
  duplicate (⊥: ωStream α) = ⊥ := by
  rw [duplicate, corec.unfold, ωStream.cases_bot]

@[simp] def ωStream.duplicate.unfold_cons (x: α) (xs: ωStream α) :
  (x ::: xs).duplicate = (x ::: xs) ::: duplicate xs := by
  rw [duplicate, corec.unfold, ωStream.cases_cons]

def ωStream.extend : (ωStream α → β) → ωStream α → ωStream β :=
  λ f x => map f (duplicate x)

@[simp] def ωStream.extend.unfold_bot (f: ωStream α → β) :
  extend f ⊥ = ⊥ := by
  rw [extend, duplicate.unfold_bot, map.unfold_bot]

@[simp] def ωStream.extend.unfold_cons
  (f: ωStream α → β) (x: α) (xs: ωStream α) :
  extend f (x ::: xs) = f (x ::: xs) ::: extend f xs := by
  rw [extend, duplicate.unfold_cons, map.unfold_cons]
  rfl

inductive ωStream.Until'
  : ωStream Prop → ωStream Prop → Prop where
| stop {P Q} (p q: Prop) (ps qs: ωStream Prop) :
  q → p ::: ps = P → q ::: qs = Q → Until' P Q
| cons {P Q} (p q: Prop) (ps qs: ωStream Prop) :
  p → Until' ps qs → p ::: ps = P → q ::: qs = Q → Until' P Q

-- P U Q := P.Until' Q ::: ∘P U ∘Q
def ωStream.Until (P: ωStream Prop) (Q: ωStream Prop) : ωStream Prop :=
  corec (λ (P, Q) =>
    F.cons (Until' P Q) (P.next, Q.next)
  ) (P, Q)

@[simp] def ωStream.Until.unfold (Q: ωStream Prop) :
  Until P Q = Until' P Q ::: Until P.next Q.next :=
  by rw [Until, corec.unfold]
     rfl


syntax:max "tprop(" term ")" : term
syntax:max "term(" term ")" : term

macro_rules
| `(tprop(term($t))) => pure t
| `(tprop($t)) => pure t

macro_rules
| `(tprop(($P))) => ``((tprop($P)))
| `(tprop($P $[ $Q]*)) => ``($P $[ $Q]*)
| `(tprop(if $c then $t else $e)) => ``(if $c then tprop($t) else tprop($e))

partial def unpackTprop
  [Monad M] [MonadRef M] [MonadQuotation M] : Term → M Term
| `(tprop($P)) => do `($P)
| `($P:ident) => do `($P)
| `(?$P:ident) => do `(?$P)
| `(($P)) => do `(($(← unpackTprop P)))
| `($P $[ $Q]*) => do ``($P $[ $Q]*)
| `(if $c then $t else $e) => do
  let t ← unpackTprop t
  let e ← unpackTprop e
  `(if $c then $t else $e)
| `(($P : $t)) => do ``(($(← unpackTprop P) : $t))
| `($t) => `($t:term)


class LTLBase (PROP: Type u) where
  Entails : PROP → PROP → Prop

  And : PROP → PROP → PROP
  Imp : PROP → PROP → PROP
  Pure : Prop → PROP
  Or : PROP → PROP → PROP
  Until : PROP → PROP → PROP
  Next : PROP → PROP

def LTLBase.Not {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP :=
  Imp p (Pure False)
def LTLBase.Iff {PROP: Type u} [LTLBase PROP] (p₁ p₂: PROP) : PROP :=
  And (Imp p₁ p₂) (Imp p₂ p₁)
def LTLBase.Diamond {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP :=
  Until (Pure True) p
def LTLBase.Square {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP :=
  Not (Diamond (Not p))

macro:25 P:term:29 " ⊢ " Q:term:25 : term =>
  ``(LTLBase.Entails tprop($P) tprop($Q)) -- type as \entails or \vdash
macro:25 " ⊢ " Q:term:25 : term =>
  ``(LTLBase.Entails (LTLBase.Pure True) tprop($Q))

delab_rule LTLBase.Entails
| `($_ $P $Q) => do ``($(← unpackTprop P) ⊢ $(← unpackTprop Q))

syntax:35 term:36 "∪" term:35: term -- type as \union
syntax:max "∘ " term:40 : term -- type as \circ
syntax:max "□ " term:40 : term -- type as \square
syntax:max "⋄ " term:40 : term -- type as \diamond
syntax "⌜" term "⌝" : term -- type as ulc and \urc
syntax "⊤" : term -- type as \top
syntax "⊥" : term -- type as \bot

macro_rules
| `(tprop($P ∧ $Q)) => ``(LTLBase.And tprop($P) tprop($Q))
| `(tprop($P ∨ $Q)) => ``(LTLBase.Or tprop($P) tprop($Q))
| `(tprop($P → $Q)) => ``(LTLBase.Imp tprop($P) tprop($Q))
| `(tprop($P ↔ $Q)) => ``(LTLBase.Iff tprop($P) tprop($Q))
| `(tprop($P ∪ $Q)) => ``(LTLBase.Until tprop($P) tprop($Q))
| `(tprop(⌜ $P ⌝)) => ``(LTLBase.Pure $P)
| `(tprop(¬$P)) => ``(LTLBase.Not tprop($P))
| `(tprop(□$P)) => ``(LTLBase.Square tprop($P))
| `(tprop(∘$P)) => ``(LTLBase.Next tprop($P))
| `(tprop(⋄$P)) => ``(LTLBase.Diamond tprop($P))
| `(tprop(⊤)) => ``(LTLBase.Pure True)
| `(tprop(⊥)) => ``(LTLBase.Pure False)

delab_rule LTLBase.And
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ∧ $(← unpackTprop Q)))
delab_rule LTLBase.Or
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ∨ $(← unpackTprop Q)))
delab_rule LTLBase.Imp
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) → $(← unpackTprop Q)))
delab_rule LTLBase.Iff
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ↔ $(← unpackTprop Q)))
delab_rule LTLBase.Until
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ∪ $(← unpackTprop Q)))
delab_rule LTLBase.Not
| `($_ $P) => do ``(tprop(¬$(← unpackTprop P)))
delab_rule LTLBase.Next
| `($_ $P) => do ``(tprop(∘$(← unpackTprop P)))
delab_rule LTLBase.Square
| `($_ $P) => do ``(tprop(□$(← unpackTprop P)))
delab_rule LTLBase.Diamond
| `($_ $P) => do ``(tprop(⋄$(← unpackTprop P)))
delab_rule LTLBase.Pure
| `($_ $P) => do ``(tprop(⌜$P⌝))

delab_rule LTLBase.Pure
| `($_ False) => do ``(tprop(⊥))
| `($_ True) => do ``(tprop(⊤))



structure LTLBase.BiEntails
  {PROP: Type u} [LTLBase PROP] (P Q: PROP) : Prop where
  mp : P ⊢ Q
  mpr: Q ⊢ P

macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term =>
  ``(LTLBase.BiEntails tprop($P) tprop($Q)) -- type as \dashv\entails

delab_rule LTLBase.BiEntails
  | `($_ $P $Q) => do ``($(← unpackTprop P) ⊣⊢ $(← unpackTprop Q))

delab_rule LTLBase.Entails
| `($_ tprop(⌜ True ⌝) $P) => do ``(⊢ $(← unpackTprop P))

#check ∀ (PROP: Type) [LTLBase PROP] (A B C D: PROP), tprop((A → ⋄B) → (C → D)) ⊢ tprop(C ∧ D)


class LTL (PROP: Type u) extends LTLBase PROP where
  entails_transitive : Transitive Entails
  entails_reflexive : Reflexive Entails

  -- This relation is false in case of finite or infinite streams
  -- bientails_iff_eq (P Q: PROP) : P ⊣⊢ Q ↔ P = Q

  -- logic reasoning

  and_elim_l {P Q: PROP} : P ∧ Q ⊢ P -- ∀ H, H ⊢ P ∧ Q → P
  and_elim_r {P Q: PROP} : P ∧ Q ⊢ Q -- ∀ H, H ⊢ P ∧ Q → Q
  and_intro {P Q R: PROP} : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R -- ∀ H, H ⊢ P → Q → P ∧ Q

  or_intro_l {P Q: PROP} : P ⊢ P ∨ Q -- ∀ H, H ⊢ P → P ∨ Q
  or_intro_r {P Q: PROP} : Q ⊢ P ∨ Q -- ∀ H, H ⊢ Q → P ∨ Q
  or_elim {P Q R: PROP} : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R -- ∀ H, H ⊢ (P → R) → (Q → R) → (P ∨ Q) → R

  imp_intro {P Q R: PROP} : (P ∧ Q ⊢ R) → P ⊢ (Q → R) -- ⊢
  imp_elim {P Q R: PROP} : (P ⊢ Q → R) → (P ∧ Q ⊢ R)

  pure_intro {ψ: Prop} {P: PROP} : ψ → (P ⊢ ⌜ ψ ⌝)
  pure_elim' {ψ: Prop} {P: PROP} : (ψ → ⊢ P) → ⌜ψ⌝ ⊢ P

  -- temporal reasoning

  next_self_dual {P: PROP} : ¬∘P ⊣⊢ ∘¬P

  next_imp_distributivity {P Q: PROP} : ⊢ ∘(P → Q) → (∘P → ∘Q)

  square_imp_distributivity {P Q: PROP} : ⊢ □(P → Q) → (□P → □Q)

  until_unfold {P Q: PROP} : P ∪ Q ⊣⊢ Q ∨ (P ∧ ∘(P ∪ Q))

  diamond_intro {P Q: PROP} : ⊢ (P ∪ Q) → ⋄Q

-- unif_hint [LTLBase PROP] (P Q : PROP) where |- tprop(P ↔ Q) ≟ tprop((P → Q) ∧ (Q → P))

def LTLBase.Entails.trans {P Q R: PROP} [LTL PROP] (h₁: P ⊢ Q) (h₂: Q ⊢ R) : P ⊢ R := LTL.entails_transitive h₁ h₂
def LTLBase.BiEntails.trans {P Q R: PROP} [LTL PROP] (h₁: P ⊣⊢ Q) (h₂: Q ⊣⊢ R) : P ⊣⊢ R := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
def LTLBase.Entails.rfl {P: PROP} [LTL PROP] : P ⊢ P := LTL.entails_reflexive P
def LTLBase.BiEntails.rfl {P: PROP} [LTL PROP] : P ⊣⊢ P := ⟨.rfl, .rfl⟩

namespace LTL
variable {PROP: Type u} [inst: LTL PROP]


def And.left {H: PROP} (P Q: PROP) : H ⊢ P ∧ Q → P :=
  imp_intro <| and_elim_r.trans and_elim_l

def And.right {H: PROP} (P Q: PROP) : H ⊢ P ∧ Q → Q :=
  imp_intro <| and_elim_r.trans and_elim_r

def And.mk {H: PROP} {P Q: PROP} : H ⊢ P → Q → P ∧ Q :=
  imp_intro <| imp_intro <| and_intro (and_elim_l.trans and_elim_r) and_elim_r

def and_top {P: PROP} : tprop(P ∧ ⊤) ⊣⊢ P := by
  constructor
  · exact and_elim_l
  · apply and_intro
    · exact .rfl
    · apply pure_intro
      trivial

def top_and {P: PROP} : tprop(⊤ ∧ P) ⊣⊢ P := by
  constructor
  · exact and_elim_r
  · apply and_intro
    · apply pure_intro
      trivial
    · exact .rfl


#check square_imp_distributivity

instance entails_trans : Trans (α := PROP) inst.Entails inst.Entails inst.Entails where
  trans h₁ h₂ := h₁.trans h₂

#check entails_trans.trans
#check LTL.and_elim_l
theorem and_elim_l' {P Q R: PROP} (h: P ⊢ R) : P ∧ Q ⊢ R := entails_trans.trans and_elim_l h
theorem and_elim_r' {P Q R: PROP} (h: Q ⊢ R) : P ∧ Q ⊢ R := entails_trans.trans and_elim_r h

theorem or_intro_l' {P Q R: PROP} (h: P ⊢ Q) : P ⊢ Q ∨ R := h.trans or_intro_l
theorem or_intro_r' {P Q R: PROP} (h: P ⊢ R) : P ⊢ Q ∨ R := h.trans or_intro_r


theorem and_symm {P Q:PROP} : P ∧ Q ⊢ Q ∧ P := and_intro and_elim_r and_elim_l
theorem mp {P Q R: PROP} (h₁: P ⊢ Q → R) (h₂: P ⊢ Q) : P ⊢ R :=
  entails_trans.trans (and_intro .rfl h₂) (imp_elim h₁)

theorem imp_intro' {P Q R: PROP} (h: Q ∧ P ⊢ R) : P ⊢ Q → R := imp_intro <| and_symm.trans h

theorem imp_elim' {P Q R : PROP} (h : Q ⊢ P → R) : P ∧ Q ⊢ R :=
  and_symm.trans <| imp_elim h

theorem imp_elim_l {P Q : PROP} : (P → Q) ∧ P ⊢ Q := imp_elim .rfl

theorem imp_elim_r {P Q : PROP} : P ∧ (P → Q) ⊢ Q := imp_elim' .rfl

theorem false_elim {P : PROP} : ⊥ ⊢ P := pure_elim' False.elim

theorem true_intro {P : PROP} : P ⊢ ⊤ := pure_intro trivial

-- @[rw_mono_rule]
theorem and_mono {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∧ P' ⊢ Q ∧ Q' :=
  and_intro (and_elim_l' h1) (and_elim_r' h2)

theorem and_mono_l {P P' Q : PROP} (h : P ⊢ P') : P ∧ Q ⊢ P' ∧ Q := and_mono h .rfl

theorem and_mono_r {P Q Q' : PROP} (h : Q ⊢ Q') : P ∧ Q ⊢ P ∧ Q' := and_mono .rfl h

--@[rw_mono_rule]
theorem and_congr {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∧ P' ⊣⊢ Q ∧ Q' :=
  ⟨and_mono h1.1 h2.1, and_mono h1.2 h2.2⟩

theorem and_congr_l {P P' Q : PROP} (h : P ⊣⊢ P') : P ∧ Q ⊣⊢ P' ∧ Q := and_congr h .rfl

theorem and_congr_r {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∧ Q ⊣⊢ P ∧ Q' := and_congr .rfl h

--@[rw_mono_rule]
theorem or_mono {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∨ P' ⊢ Q ∨ Q' :=
  or_elim (or_intro_l' h1) (or_intro_r' h2)

theorem or_mono_l {P P' Q : PROP} (h : P ⊢ P') : P ∨ Q ⊢ P' ∨ Q := or_mono h .rfl

theorem or_mono_r {P Q Q' : PROP} (h : Q ⊢ Q') : P ∨ Q ⊢ P ∨ Q' := or_mono .rfl h

--@[rw_mono_rule]
theorem or_congr {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∨ P' ⊣⊢ Q ∨ Q' :=
  ⟨or_mono h1.1 h2.1, or_mono h1.2 h2.2⟩

theorem or_congr_l {P P' Q : PROP} (h : P ⊣⊢ P') : P ∨ Q ⊣⊢ P' ∨ Q := or_congr h .rfl

theorem or_congr_r {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∨ Q ⊣⊢ P ∨ Q' := or_congr .rfl h

--@[rw_mono_rule]
theorem imp_mono {P P' Q Q' : PROP} (h1 : Q ⊢ P) (h2 : P' ⊢ Q') : (P → P') ⊢ Q → Q' :=
  imp_intro <| (and_mono_r h1).trans <| (imp_elim .rfl).trans h2

theorem imp_mono_l {P P' Q : PROP} (h : P' ⊢ P) : (P → Q) ⊢ (P' → Q) := imp_mono h .rfl

theorem imp_mono_r {P Q Q' : PROP} (h : Q ⊢ Q') : (P → Q) ⊢ (P → Q') := imp_mono .rfl h

--@[rw_mono_rule]
theorem imp_congr {P P' Q Q' : PROP}
    (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : (P → P') ⊣⊢ (Q → Q') :=
  ⟨imp_mono h1.2 h2.1, imp_mono h1.1 h2.2⟩

theorem imp_congr_l {P P' Q : PROP} (h : P ⊣⊢ P') : (P → Q) ⊣⊢ (P' → Q) :=
  imp_congr h .rfl

theorem imp_congr_r {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P → Q) ⊣⊢ (P → Q') :=
  imp_congr .rfl h

theorem and_self {P : PROP} : P ∧ P ⊣⊢ P := ⟨and_elim_l, and_intro .rfl .rfl⟩
--instance : Idempotent (α := PROP) BiEntails and := ⟨and_self⟩

theorem or_self {P : PROP} : P ∨ P ⊣⊢ P := ⟨or_elim .rfl .rfl, or_intro_l⟩
--instance : Idempotent (α := PROP) BiEntails or := ⟨or_self⟩

theorem and_comm {P : PROP} : P ∧ Q ⊣⊢ Q ∧ P := ⟨and_symm, and_symm⟩
--instance : Commutative (α := PROP) BiEntails and := ⟨and_comm⟩

theorem true_and {P : PROP} : ⊤ ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
--instance : LeftId (α := PROP) BiEntails tprop(True) and := ⟨true_and⟩

theorem and_true {P : PROP} : P ∧ ⊤ ⊣⊢ P := and_comm.trans true_and
--instance : RightId (α := PROP) BiEntails tprop(True) and := ⟨and_true⟩

theorem and_assoc {P Q R : PROP} : (P ∧ Q) ∧ R ⊣⊢ P ∧ Q ∧ R :=
  ⟨and_intro (and_elim_l' and_elim_l) (and_mono_l and_elim_r),
   and_intro (and_mono_r and_elim_l) (and_elim_r' and_elim_r)⟩

end LTL

instance ωStream.instLTLBase : LTLBase (ωStream Prop) where
  Entails := ωStream.Entails
  And := ωStream.and
  Imp := ωStream.imp
  Pure := ωStream.const
  Or := ωStream.or
  Until := ωStream.Until
  Next := ωStream.next

theorem ωStream.entails_reflexive
  (P: ωStream Prop) : P ⊢ P := by
  coinduction generalizing [P] using ωStream.Entails.coind
  intro l r ⟨P, eq₁, eq₂, _⟩
  induction eq₁
  induction eq₂
  cases P
  case bot =>
    apply Entails.F.BotLeft
  case cons p ps =>
    apply Entails.F.cons p p ps ps
    · intro h
      exact h
    · exists ps
    · rfl
    · rfl

--theorem ωStream.entails_transitive (P Q R: ωStream Prop) :
--  (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R) := by
