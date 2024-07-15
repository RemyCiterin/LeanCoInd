
import Lean.PrettyPrinter.Delaborator
import CoInd.Std.DelabRule
import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils
import CoInd.Stream.LTLBase
import CoInd.Stream.Expr
import CoInd.Stream.Tactics.Intro


import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq


open Lean Lean.Macro Lean.Expr Lean.Meta Qq Elab.Tactic Elab
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

example (PROP: Type) [LTL PROP] (P Q R: PROP) :
  (P ∧ Q ∧ R ∧ □⊤) ∨ P ⊢ ⋄P → P ∧ Q → P := by
  tstart
  tintro ⟨⟨h₁, h₂, h₃, h₄⟩ | h₁⟩ h₅
  . tintro ⟨h₇, h₈⟩
    sorry
  . tintro ⟨h₆, h₇⟩
    sorry


#check ∀ (prop: Q(Type)) (_: Q(LTL $prop)) (P R: Q($prop)), Q($P ⊢ $R)
#check ∀ (P R: Q(Prop)), Q($P → $R)
