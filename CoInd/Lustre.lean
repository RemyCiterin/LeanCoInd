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

instance {I: Type u} {α: I → Type v} [∀ i, Preorder (α i)] [∀ i, OrderBot (α i)] : OrderBot (∀ i, α i) where
  bot_le := by
    intro f x
    apply bot_le

instance {α: Type u} : OrderBot (Kahn α) where
  bot_le := Kahn.bot_le


namespace Lustre

structure Env where
  var : Type u
  type : var → Type u

@[simp]
def Env.add.var (A B: Env.{u}) : Type u := A.var ⊕ B.var

@[simp]
def Env.add.type (A B: Env.{u}) : Env.add.var A B → Type u
| .inl a => A.type a
| .inr b => B.type b

abbrev Str (A: Env.{u}) := ∀ a: A.var, Kahn (A.type a)

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

def Node.ensure {I O: Env} (node: Node I O) (P: Admissible (Str I)) (Q: Admissible (Str O)) : Prop :=
  ∀ (i: Str I), i ∈ P → node.eval i ∈ Q

#check Admissible.FixCont_thm

@[refinment_type] def Node.prove  {I O: Env} (node: Node I O) (P: Admissible (Str I)) (Q: Admissible (Str O)) (Inv: Admissible (Str node.L))
  (hyp: ∀ (i: Str I) (l: Str node.L), i ∈ P → l ∈ Inv → node.eqs i l ∈ Inv ∧ node.out i l ∈ Q) : node.ensure P Q := by
  intro i h₁
  have h₃ : ContinuousHom.fix (node.eqs i) ∈ Inv := by
    refinment_type
    intro l h₂
    apply (hyp _ _ h₁ h₂).left
  apply (hyp _ _ h₁ h₃).right




end Lustre
