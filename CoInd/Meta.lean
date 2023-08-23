import Lean
import CoInd.M

open Lean Elab Meta Expr

/-
definition of coinductive types of the form

codata Name (x₁: t₁) ... (xₙ: tₙ) where
| C₁ : (y₁₁: t₁₁) → ... (y₁ₘ: t₁ₘ) → Name
.
.
.
| Cₖ : (yₖ₁: tₖ₁) → ... → (yₖₗ: tₖₗ) → Name

with tᵢⱼ of the form
| (x₁: a₁) → ... → (xₙ: aₙ) → Name
| t
-/

namespace Lean.Elab.Command.CoInd


declare_syntax_cat codata_binder

syntax " ( " ident " : " term " ) " : codata_binder
syntax codata_binders := codata_binder*

declare_syntax_cat codata_ctor

syntax " | " ident " : " term : codata_ctor
syntax " |  " ident : codata_ctor

syntax codata_ctors := codata_ctor*

syntax " codata " ident codata_binders " where " codata_ctors : command

#check Lean.Elab.Term.elabTerm
#check inferType

def parseBinder : Syntax → MacroM (Name × Syntax)
  | `(codata_binder| ( $i:ident : $t:term )) => do
    return (i.getId, t)
  | s => throw <| .error s "not a valid binder of the form `(i: t)`"

partial def parseBinders : Syntax → MacroM (Array (Name × Syntax))
  | `(codata_binders| $b:codata_binder*) => Array.mapM parseBinder b
  | s => throw <| .error s "not a valid binder of the form (x₁:t₁) ... (xₙ:tₙ)"

#check expandMacros

structure CtorView where
  ref: Syntax
  declName: Name
  expr: Syntax
  deriving Inhabited

partial def parseCtor (name:Name) (s:Syntax) : MacroM (CtorView) :=
  match s with
  | `(codata_ctor| | $i:ident : $t:term) => do
    let t: Syntax ← expandMacros t
    return ⟨s, i.getId, t⟩
  | `(codata_ctor| | $i:ident) => do
    return ⟨s, i.getId, mkIdent name⟩
  | _ => throw <| .error s "not a valid constructor"

partial def parseCtors (name:Name) : Syntax → MacroM (Array CtorView)
  | `(codata_ctors| $a:codata_ctor*) => Array.mapM (parseCtor name) a
  | s => throw <| .error s "not a valid constructor"

structure CoIndView where
  ref: Syntax
  declName: Name
  binders: Array (Name × Syntax)
  ctors: Array CtorView
  deriving Inhabited

partial def parseCoInd (s:Syntax) : MacroM CoIndView :=
  match s with
  | `(command| codata $name:ident $b:codata_binders where $ctors:codata_ctors) => do
    return ⟨s, name.getId, ←parseBinders b, ←parseCtors name.getId ctors⟩
  | s => throw <| .error s "not a valid codata"

def CoIndView.genFunctor (data:CoIndView) : MacroM Syntax := do
  `(command| inductive $(mkIdent <| Name.str data.declName "Functor") where)

#print Name

macro_rules
| `(command| codata $name:ident $b:codata_binders where $ctors:codata_ctors) => do
  let s: Syntax ← `(command| codata $name:ident $b:codata_binders where $ctors:codata_ctors)
  have c: CoIndView := ⟨s, name.getId, ←parseBinders b, ←parseCtors name.getId ctors⟩
  CoIndView.genFunctor c


codata f where

#print f.Functor



end Lean.Elab.Command.CoInd
