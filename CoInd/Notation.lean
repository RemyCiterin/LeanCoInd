-- This file allow to define elements of a CCC using a "symply typed lambda calculus syntax"
import Lean
import CoInd.OmegaCompletePartialOrder

open Lean Elab Meta

#print Expr


declare_syntax_cat mini_term
syntax num : mini_term
syntax "[" term "]" : mini_term
syntax "(" mini_term ")" : mini_term
syntax "λ" mini_term "end" : mini_term
syntax mini_term mini_term : mini_term

syntax "CCC(" mini_term ")" : term

#check OmegaCompletePartialOrder.ContinuousHom.const
#check OmegaCompletePartialOrder.ContinuousHom.Prod.fst
#check OmegaCompletePartialOrder.ContinuousHom.Prod.snd
#check OmegaCompletePartialOrder.ContinuousHom.Prod.prod

#check OmegaCompletePartialOrder.ContinuousHom.Prod.curry.hom
#check OmegaCompletePartialOrder.ContinuousHom.Prod.curry.inv
#check OmegaCompletePartialOrder.ContinuousHom.comp
#check OmegaCompletePartialOrder.ContinuousHom.id

#print TSyntax.getNat

def CCC.mkArg : Nat → MacroM (TSyntax `term)
| 0 => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.snd)
| n+1 => do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      $(←mkArg n) OmegaCompletePartialOrder.ContinuousHom.Prod.fst)


macro_rules
| `(term| CCC($n:num)) => CCC.mkArg n.getNat
| `(term| CCC([$t:term])) =>
  `(term| OmegaCompletePartialOrder.ContinuousHom.const $t)
| `(term| CCC(λ $t:mini_term end)) =>
  `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.curry CCC($t))
| `(term| CCC(($t:mini_term))) => `(term| CCC($t))
| `(term| CCC($t₁:mini_term $t₂:mini_term)) =>
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      (OmegaCompletePartialOrder.ContinuousHom.Prod.curry.symm CCC($t₁))
      (OmegaCompletePartialOrder.ContinuousHom.Prod.prod
        OmegaCompletePartialOrder.ContinuousHom.id
        CCC($t₂)
      )
  )


variable {α β: Type u} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

open OmegaCompletePartialOrder.ContinuousHom
open OmegaCompletePartialOrder

#check CCC(λ [(ContinuousHom.Prod.fst : α × β →𝒄 α)] end)
example (x: β) (y z: α) : (CCC(λ λ 1 end end) : β →𝒄 α →𝒄 α →𝒄 α) x y z = y := by
  rfl
