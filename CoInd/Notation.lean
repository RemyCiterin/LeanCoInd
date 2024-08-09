-- This file allow to define elements of a CCC using a "symply typed lambda calculus syntax"
import Lean
import CoInd.OmegaCompletePartialOrder
import Batteries

open Lean Elab Meta

/- A syntax to declare continuous functions using a "lambda calculous" notation -/
declare_syntax_cat cont_term
declare_syntax_cat cont_term1
syntax cont_term1 : cont_term
syntax ident : cont_term1
syntax "{" term "}" : cont_term1
syntax "(" cont_term ")" : cont_term1
syntax "(" cont_term ":" term ")" : cont_term1
syntax "λᶜ" explicitBinders "=>" cont_term : cont_term
syntax "λᶜ" explicitBinders "=>" cont_term : term
syntax cont_term1 "(" cont_term,* ")" : cont_term1

inductive ContTerm.Ast where
| lambda : Ident → Option Term → Ast → Ast -- variable name and type
| ident : Ident → Ast -- we must search if the ident is a variable
| showFrom : Ast → Term → Ast
| app : Ast → Ast → Ast
| term : Term → Ast

instance : Inhabited ContTerm.Ast where
  default := .ident (mkIdent `foo)

open TSyntax.Compat in
def ContTerm.parseExplicitBindersAux (idents : Array Syntax) (type? : Option Syntax) (acc: List (Ident × Option Term))
  : MacroM (List (Ident × Option Term)) :=
  let rec loop (i : Nat) (acc : List (Ident × Option Term)) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let ident := idents[i]![0]
      let acc := match ident.isIdent, type? with
        | true,  none      => (ident, none) :: acc
        | true,  some type => (ident, some type) :: acc
        | false, none      => (mkIdent `_, none) :: acc
        | false, some type => (mkIdent `_, some type) :: acc
      loop i acc
  loop idents.size acc

def ContTerm.parseBrackedBindersAux (binders : Array Syntax) (acc: List (Ident × Option Term))
  : MacroM (List (Ident × Option Term)) :=
  let rec loop (i : Nat) (acc : List (Ident × Option Term)) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let idents := binders[i]![1].getArgs
      let type   := binders[i]![3]
      loop i (← parseExplicitBindersAux idents (some type) acc)
  loop binders.size acc

partial def ContTerm.parseBinders (explicitBinders: Syntax) : MacroM (List (Ident × Option Term)) := do
  let explicitBinders := explicitBinders[0]
  if explicitBinders.getKind == ``Lean.unbracketedExplicitBinders then
    let idents   := explicitBinders[0].getArgs
    let type? := if explicitBinders[1].isNone then none else some explicitBinders[1][1]
    parseExplicitBindersAux idents type? []
  else if explicitBinders.getArgs.all (·.getKind == ``Lean.bracketedExplicitBinders) then
    parseBrackedBindersAux explicitBinders.getArgs []
  else
    Macro.throwError "unexpected explicit binder"

#check List.foldlM

mutual
partial def ContTerm.Ast.parse : TSyntax `cont_term → MacroM ContTerm.Ast
| `(cont_term| λᶜ $b:explicitBinders => $body:cont_term) => do
  let list ← parseBinders b
  return List.foldr (λ (i, t) body => .lambda i t body) (←parse body) list
| `(cont_term| $t:cont_term1) => parse1 t
| t => Macro.throwError s!"invalid continuous function {t}"

partial def ContTerm.Ast.parse1 : TSyntax `cont_term1 → MacroM ContTerm.Ast
| `(cont_term1| {$t:term}) => return .term t
| `(cont_term1| ($t:cont_term)) => parse t
| `(cont_term1| ($x:cont_term : $t:term)) => do
  return .showFrom (←parse x) t
| `(cont_term1| $t₁:cont_term1 ($t₂:cont_term,*)) => do
  have t₂: Array (TSyntax `cont_term) := t₂
  List.foldlM (λ f arg => do return ContTerm.Ast.app f (← parse arg)) (←parse1 t₁) t₂.toList
| `(cont_term1| $i:ident) => return .ident i
| t => Macro.throwError s!"invalid continuous function {t}"
end

inductive ContTerm.IR where
| lambda : Option Term → IR → IR
| showFrom : IR → Term → IR
| app : IR → IR → IR
| term : Term → IR
| arg : Nat → IR

def ContTerm.mkArg : Nat → MacroM (TSyntax `term)
| 0 => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.snd)
| n+1 => do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      $(←mkArg n) OmegaCompletePartialOrder.ContinuousHom.Prod.fst)

def ContTerm.IR.toTerm : IR → MacroM Term
| .arg n => mkArg n
| .showFrom ir t => do
  `(term| ($(←toTerm ir) : _ →𝒄 $t))
| .term t =>
  `(term| OmegaCompletePartialOrder.ContinuousHom.const $t)
| .lambda .none body => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.curry $(←toTerm body))
| .lambda (.some t) body => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.curry ($(←toTerm body) : _ × $t →𝒄 _))
| .app lhs rhs => do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      (OmegaCompletePartialOrder.ContinuousHom.Prod.curry.symm $(←toTerm lhs))
      (OmegaCompletePartialOrder.ContinuousHom.Prod.prod
        OmegaCompletePartialOrder.ContinuousHom.id
        $(←toTerm rhs)
      )
  )

#check OmegaCompletePartialOrder.ContinuousHom.Prod.curry.hom

def ContTerm.IR.toString : IR → String
| .lambda t ir => s!"λᶜ {t} => {toString ir}"
| .showFrom ir t => s!"({toString ir} : {t})"
| .app lhs rhs => s!"({toString lhs} {toString rhs})"
| .term t => s!"`({t})"
| .arg n => s!"{n}"

instance : ToString ContTerm.IR := ⟨ContTerm.IR.toString⟩

#check List.findIdxs
#print Term
def ContTerm.Ast.compile (env: List Ident) : ContTerm.Ast → ContTerm.IR
| .lambda name type output =>
  .lambda type (compile (name :: env) output)
| .showFrom ast type =>
  .showFrom (compile env ast) type
| .term t =>
  .term t
| .app lhs rhs =>
  .app (compile env lhs) (compile env rhs)
| .ident name =>
  if let idx :: _ := List.findIdxs (λ n => n == name) env
  then .arg idx
  else .term name

macro_rules
| `(term| λᶜ $b:explicitBinders => $body:cont_term) => do
  let list ← ContTerm.parseBinders b
  let ast := List.foldr (λ (i, t) body => ContTerm.Ast.lambda i t body) (←ContTerm.Ast.parse body) list
  let ir : ContTerm.IR := ContTerm.Ast.compile [] ast
  `(term| $(← ir.toTerm) Unit.unit)

open OmegaCompletePartialOrder
open ContinuousHom

#check
  λᶜ (x : Unit ⊕ Empty) (y : _) =>
    ContinuousHom.Prod.fst({ContinuousHom.Prod.mk}(x, y))
