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
import CoInd.Kahn


open OmegaCompletePartialOrder

instance {I: Type u} {α: I → Type v} [∀ i, Preorder (α i)] [∀ i, OrderBot (α i)]
  : OrderBot (∀ i, α i) where
  bot_le := by
    intro f x
    apply bot_le

instance {α: Type u} : OrderBot (Kahn α) where
  bot_le := Kahn.bot_le


namespace OmegaCompletePartialOrder.Admissible

instance {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α] : Top (Admissible α) where
  top :=
    ⟨
      λ _ => True,
      by intro _ _; trivial,
      by trivial
    ⟩

-- using a function from (x: α) to a set of admissible property over (β x), construct
-- an admissible property over ((x: α) → β x)
def foreach {α: Type u} {β: α → Type v} [∀ x, OmegaCompletePartialOrder (β x)] [∀ x, OrderBot (β x)]
  (P : ∀ x, Admissible (β x)) : Admissible (∀ x, β x) where
  toSet f := ∀ x, f x ∈ P x
  contain_bot := by
    intro x
    apply contain_bot
  admissible' := by
    intro chain h₁ x
    apply admissible
    intro n
    apply h₁

@[refinment_type]
def foreach.apply {α: Type u} {β: α → Type v} [∀ x, OmegaCompletePartialOrder (β x)] [∀ x, OrderBot (β x)]
  (P : ∀ x, Admissible (β x)) (f: ∀ x, β x) (hyp: ∀ x, f x ∈ P x) : f ∈ foreach P := hyp

def prod {α: Type u} {β: Type v}
  [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [OrderBot α] [OrderBot β]
  (P: Admissible α) (Q: Admissible β) : Admissible (α × β) where
  toSet pair := pair.fst ∈ P ∧ pair.snd ∈ Q
  admissible' := by
    intro chain h₁
    constructor
    · apply admissible
      intro n
      apply (h₁ n).left
    · apply admissible
      intro n
      apply (h₁ n).right
  contain_bot := by
    constructor
    · apply contain_bot
    · apply contain_bot

@[refinment_type]
def prod.apply {α: Type u} {β: Type v}
  [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [OrderBot α] [OrderBot β]
  (P: Admissible α) (Q: Admissible β) (a: α) (b: β) (h₁: a ∈ P) (h₂: b ∈ Q) : (a, b) ∈ prod P Q :=
  ⟨h₁, h₂⟩

#check ContinuousHom.Prod.curry

@[refinment_type]
def elim_curry {α: Type u} {β: Type v} {γ: Type w}
  [OmegaCompletePartialOrder α]
  [OmegaCompletePartialOrder β]
  [OmegaCompletePartialOrder γ]
  [OrderBot α] (P: Admissible α)
  (b: β) (c: γ) (f: β × γ →𝒄 α) :
  f (b, c) ∈ P → ContinuousHom.Prod.curry f b c ∈ P := by
  intro h
  apply h

@[refinment_type]
def elim_uncurry {α: Type u} {β: Type v} {γ: Type w}
  [OmegaCompletePartialOrder α]
  [OmegaCompletePartialOrder β]
  [OmegaCompletePartialOrder γ]
  [OrderBot α] (P: Admissible α)
  (b: β) (c: γ) (f: β →𝒄 γ →𝒄 α) :
  f b c ∈ P → ContinuousHom.Prod.curry.symm f (b, c) ∈ P := by
  intro h
  apply h

@[refinment_type]
def elim_comp {α: Type u} {β: Type v} {γ: Type w}
  [OmegaCompletePartialOrder α]
  [OmegaCompletePartialOrder β]
  [OmegaCompletePartialOrder γ]
  [OrderBot α] (P: Admissible α)
  (c: γ) (f: γ →𝒄 β) (g: β →𝒄 α) :
  g (f c) ∈ P → ContinuousHom.comp g f c ∈ P := by
  intro h
  apply h



end OmegaCompletePartialOrder.Admissible


namespace Lustre

structure Env where
  var : Type u
  type : var → Type u

def Env.State (E: Env.{u}) := (v: E.var) → E.type v

@[simp]
def Env.add.var (A B: Env.{u}) : Type u := A.var ⊕ B.var

@[simp]
def Env.add.type (A B: Env.{u}) : Env.add.var A B → Type u
| .inl a => A.type a
| .inr b => B.type b

abbrev Str (A: Env.{u}) := ∀ a: A.var, Kahn (A.type a)

inductive Square.SetF {α: Type u} (P: Set α)
  (aux: Set (Kahn α)) (s: Kahn α) : Prop where
| bot : ⊥ = s → SetF P aux s
| cons x xs : x ::: xs = s → P x → aux xs → SetF P aux s

@[simps! coe]
def Square.SetF_mono {α: Type u} (P: Set α) : (Kahn α → Prop) →o (Kahn α → Prop) where
  toFun aux x := Square.SetF P aux x
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


noncomputable def Square {α: Type u} (P: Set α) : Admissible (Kahn α) where
  toSet s := pgfp (Square.SetF_mono P) ⊥ s

  admissible' := by
    intro chain h₁
    coinduction [h₁] generalizing [chain] using pgfp.theorem (Square.SetF_mono P)
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

  contain_bot := by
    rw [←pgfp.unfold]
    apply Square.SetF.bot
    rfl

#check pgfp.unfold

@[refinment_type]
def Square.unfold_cons {α: Type u} (P: Set α) (x: α) (xs: Kahn α) :
  x ∈ P → xs ∈ Square P → x ::: xs ∈ Square P := by
  intro h₁ h₂
  simp only [Square, Membership.mem]
  rw [←pgfp.unfold]
  apply Square.SetF.cons x xs rfl h₁ (Or.inr h₂)

@[refinment_type]
def Square.unfold_bot {α: Type u} (P: Set α) :
  ⊥  ∈ Square P := by
  simp only [Square, Membership.mem]
  rw [←pgfp.unfold]
  apply Square.SetF.bot rfl

def Square.coind {α: Type u} (P: Set α) (hyp: Kahn α → Prop) :
  (∀ x, hyp x → Square.SetF P (λ x => hyp x ∨ x ∈ Square P) x)
  → ∀ x, hyp x → x ∈ Square P := by
  intro h₁ x h₂
  simp only [Membership.mem, Square]
  apply pgfp.theorem _ hyp
  clear h₂ x
  intro x h₂
  specialize h₁ x h₂
  have : (fun x => hyp x ∨ x ∈ Square P) ≤ hyp ⊔ (pgfp (SetF_mono P)) hyp := by
    intro x h₁
    cases h₁ with
    | inl h => apply Or.inl h
    | inr h =>
      apply Or.inr
      apply (pgfp (SetF_mono P)).monotone bot_le
      exact h
  apply (SetF_mono P).monotone this
  apply h₁
  apply h₂


instance : Add Env where
  add lhs rhs := ⟨Env.add.var lhs rhs, Env.add.type lhs rhs⟩

structure Node (I O: Env) where
  L : Env
  eqs : Str I →𝒄 Str L →𝒄 Str L
  out : Str I →𝒄 Str L →𝒄 Str O

noncomputable def Node.eval {I O: Env} (node: Node I O) : Str I →𝒄 Str O :=
  --λᶜ i => {node.out}(i)({ContinuousHom.fix.comp node.eqs}(i))
  (ContinuousHom.Prod.curry.symm node.out).comp
    (ContinuousHom.Prod.prod
      ContinuousHom.id
      (ContinuousHom.fix.comp node.eqs)
    )

def Node.ensure {I O: Env} (node: Node I O)
  (P: Admissible (Str I)) (Q: Admissible (Str O)) : Prop :=
  ∀ (i: Str I), i ∈ P → node.eval i ∈ Q

@[refinment_type] def Node.induction {I O: Env} (node: Node I O)
  (P: Admissible (Str I)) (Q: Admissible (Str O)) (Inv: Admissible (Str node.L))
  (hyp: ∀ (i: Str I) (l: Str node.L), i ∈ P → l ∈ Inv → node.eqs i l ∈ Inv ∧ node.out i l ∈ Q)
  : node.ensure P Q := by
  intro i h₁
  have h₃ : ContinuousHom.fix (node.eqs i) ∈ Inv := by
    refinment_type
    intro l h₂
    apply (hyp _ _ h₁ h₂).left
  apply (hyp _ _ h₁ h₃).right


namespace Test

inductive I.var : Type where
| i

abbrev I.type : I.var → Type
| .i => ℕ

abbrev I : Env := ⟨I.var, I.type⟩

inductive O.var : Type where
| o

abbrev O.type : O.var → Type
| .o => ℕ

abbrev O : Env := ⟨O.var, O.type⟩

inductive L.var : Type where
| x | y | z

abbrev L.type : L.var → Type
| .x => ℕ
| .y => Bool
| .z => Bool

abbrev L : Env := ⟨L.var, L.type⟩

open Pi.OmegaCompletePartialOrder

#check ContinuousHom.Kahn.tup

abbrev ContinuousHom.Kahn.add {α: Type u} [Add α] : Kahn α →𝒄 Kahn α →𝒄 Kahn α :=
  λᶜ x y => {ContinuousHom.Kahn.map (Function.uncurry Add.add)}(ContinuousHom.Kahn.tup(x, y))

def proj.i : Str I →𝒄 Kahn (I.type I.var.i) := proj .i

def Eqs : (l: L.var) → Str I →𝒄 Str L →𝒄 Kahn (L.type l)
| .x => λᶜ i l => ContinuousHom.Kahn.add(proj.i(i), {proj L.var.x}(l))
| .y => λᶜ i l => {proj L.var.z}(l)
| .z => λᶜ i l => {proj L.var.y}(l)

def Out : (o: O.var) → Str I →𝒄 Str L →𝒄 Kahn (O.type o)
| .o => λᶜ i l => {proj L.var.x}(l)


#check map
#check lift
#check proj

#check ContinuousHom.Prod.curry

def eqs : Str I →𝒄 Str L →𝒄 Str L :=
  ContinuousHom.Prod.curry (foreach (λ v => ContinuousHom.Prod.curry.symm (Eqs v)))

@[simp] def eqs.apply (input: Str I) (loc: Str L) (l: L.var) : eqs input loc l = Eqs l input loc := rfl

def out : Str I →𝒄 Str L →𝒄 Str O :=
  ContinuousHom.Prod.curry (foreach (λ v => ContinuousHom.Prod.curry.symm (Out v)))

@[simp] def out.apply (input: Str I) (loc: Str L) (v: O.var) : out input loc v = Out v input loc := rfl

@[simps! L eqs out]
def node : Node I O where
  L := L
  eqs := eqs
  out := out

noncomputable def node.spec.Input : (x: I.var) → Admissible (Kahn (I.type x))
| .i => Square (λ x => x > 0)

noncomputable def node.spec.Output : (x: O.var) → Admissible (Kahn (O.type x))
| .o => Square (λ x => x > 0)

noncomputable def node.spec.Local : (v: L.var) → Admissible (Kahn (L.type v))
| .x => Square (λ x => x > 0)
| .y => ⊤
| .z => ⊤


def node.proof : node.ensure (Admissible.foreach node.spec.Input) (Admissible.foreach node.spec.Output) := by
  apply Node.induction node _ _ (Admissible.foreach node.spec.Local)
  intro i l h₁ h₂
  constructor
  · refinment_type
    intro var
    cases var with
    | x =>
      simp? [Eqs]
      simp? [proj.i]
      specialize h₁ .i
      specialize h₂ .x
      generalize i I.var.i = input at *
      generalize l L.var.x = loc at *
      cases input with
      | bot =>
        simp?
        refinment_type
      | cons x xs =>
        cases loc with
        | bot =>
          simp?
          refinment_type
        | cons y ys =>
          simp? [spec.Local]
          sorry

    | y =>
      trivial
    | z =>
      trivial
  · refinment_type
    intro var
    cases var with
    | o =>
      simp [Out]
      apply h₂

end Test

end Lustre
