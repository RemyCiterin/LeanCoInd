-- This file allow to define elements of a CCC using a "symply typed lambda calculus syntax"
import Lean
import CoInd.OmegaCompletePartialOrder
import Batteries

open Lean Elab Meta


structure CCCTerm.Config where
  arrow : Ident
  product : Ident

  id : Ident
  comp : Ident
  const : Ident
  curry : Ident
  uncurry : Ident
  prod : Ident
  fst : Ident
  snd : Ident

def CCCTerm.Config.ContinuousHom : Config where
  arrow := mkIdent `OmegaCompletePartialOrder.ContinuousHom
  product := mkIdent `Prod

  id := mkIdent `OmegaCompletePartialOrder.ContinuousHom.id
  comp := mkIdent `OmegaCompletePartialOrder.ContinuousHom.comp
  curry := mkIdent `OmegaCompletePartialOrder.ContinuousHom.Prod.curry
  uncurry := mkIdent `OmegaCompletePartialOrder.ContinuousHom.Prod.curry.symm
  prod := mkIdent `OmegaCompletePartialOrder.ContinuousHom.Prod.prod
  fst := mkIdent `OmegaCompletePartialOrder.ContinuousHom.Prod.fst
  snd := mkIdent `OmegaCompletePartialOrder.ContinuousHom.Prod.snd
  const := mkIdent `OmegaCompletePartialOrder.ContinuousHom.const

@[simps! coe]
def OrderHom.const' {α: Type u} {β: Type v} [Preorder α] [Preorder β] (x: α) : β →o α where
  toFun _ := x
  monotone' _ _ _ := le_refl x

def CCCTerm.Config.OrderHom : Config where
  arrow := mkIdent `OrderHom
  product := mkIdent `Prod

  id := mkIdent `OrderHom.id
  comp := mkIdent `OrderHom.comp
  curry := mkIdent `OrderHom.curry
  uncurry := mkIdent `OrderHom.curry.symm
  prod := mkIdent `OrderHom.prod
  fst := mkIdent `OrderHom.fst
  snd := mkIdent `OrderHom.snd
  const := mkIdent `OrderHom.const'

/- A syntax to declare continuous functions using a "lambda calculous" notation -/
declare_syntax_cat ccc_term
declare_syntax_cat ccc_term1
syntax ccc_term1 : ccc_term
syntax ident : ccc_term1
syntax "{" term "}" : ccc_term1
syntax "(" ccc_term ")" : ccc_term1
syntax "(" ccc_term ":" term ")" : ccc_term1
syntax "λᶜᶜᶜ" explicitBinders "=>" ccc_term : ccc_term
syntax "λᶜᶜᶜ" explicitBinders "=>" ccc_term : term
syntax ccc_term1 "(" ccc_term,* ")" : ccc_term1

inductive CCCTerm.Ast where
| lambda : Ident → Option Term → Ast → Ast -- variable name and type
| ident : Ident → Ast -- we must search if the ident is a variable
| showFrom : Ast → Term → Ast
| app : Ast → Ast → Ast
| term : Term → Ast

instance : Inhabited CCCTerm.Ast where
  default := .ident (mkIdent `foo)

open TSyntax.Compat in
def CCCTerm.parseExplicitBindersAux (idents : Array Syntax) (type? : Option Syntax) (acc: List (Ident × Option Term))
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

def CCCTerm.parseBrackedBindersAux (binders : Array Syntax) (acc: List (Ident × Option Term))
  : MacroM (List (Ident × Option Term)) :=
  let rec loop (i : Nat) (acc : List (Ident × Option Term)) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let idents := binders[i]![1].getArgs
      let type   := binders[i]![3]
      loop i (← parseExplicitBindersAux idents (some type) acc)
  loop binders.size acc

partial def CCCTerm.parseBinders (explicitBinders: Syntax) : MacroM (List (Ident × Option Term)) := do
  let explicitBinders := explicitBinders[0]
  if explicitBinders.getKind == ``Lean.unbracketedExplicitBinders then
    let idents   := explicitBinders[0].getArgs
    let type? := if explicitBinders[1].isNone then none else some explicitBinders[1][1]
    parseExplicitBindersAux idents type? []
  else if explicitBinders.getArgs.all (·.getKind == ``Lean.bracketedExplicitBinders) then
    parseBrackedBindersAux explicitBinders.getArgs []
  else
    Macro.throwError "unexpected explicit binder"

mutual
partial def CCCTerm.Ast.parse : TSyntax `ccc_term → MacroM CCCTerm.Ast
| `(ccc_term| λᶜᶜᶜ $b:explicitBinders => $body:ccc_term) => do
  let list ← parseBinders b
  return List.foldr (λ (i, t) body => .lambda i t body) (←parse body) list
| `(ccc_term| $t:ccc_term1) => parse1 t
| t => Macro.throwError s!"invalid ccc function {t}"

partial def CCCTerm.Ast.parse1 : TSyntax `ccc_term1 → MacroM CCCTerm.Ast
| `(ccc_term1| {$t:term}) => return .term t
| `(ccc_term1| ($t:ccc_term)) => parse t
| `(ccc_term1| ($x:ccc_term : $t:term)) => do
  return .showFrom (←parse x) t
| `(ccc_term1| $t₁:ccc_term1 ($t₂:ccc_term,*)) => do
  have t₂: Array (TSyntax `ccc_term) := t₂
  List.foldlM (λ f arg => do return CCCTerm.Ast.app f (← parse arg)) (←parse1 t₁) t₂.toList
| `(ccc_term1| $i:ident) => return .ident i
| t => Macro.throwError s!"invalid ccc function1 {t}"
end

inductive CCCTerm.IR where
| lambda : Option Term → IR → IR
| showFrom : IR → Term → IR
| app : IR → IR → IR
| term : Term → IR
| arg : Nat → IR

def CCCTerm.mkArg (config: Config) (depth: ℕ) : Nat → MacroM (TSyntax `term)
| 0 => do
  -- at depth 1 the only free variable has value 0
  if depth = 1
  then `(term| $config.id)
  else `(term| $config.snd)
| n+1 => do
  `(term|
    $config.comp
      $(←mkArg config (depth-1) n) $config.fst)

def CCCTerm.IR.toTerm (config: Config) (depth: ℕ) : IR → MacroM Term
| .arg n => mkArg config depth n
| .showFrom ir t => do
  `(term| ($(←toTerm config depth ir) : $config.arrow _ $t))
| .term t => do
  `(term| $config.const $t)
| .lambda .none body => do
  if depth = 0
  then `(term| $(←toTerm config (depth+1) body))
  else `(term| $config.curry $(←toTerm config (depth+1) body))
| .lambda (.some t) body => do
  if depth = 0
  then `(term| ($(←toTerm config (depth+1) body) : $config.arrow $t _))
  else `(term| $config.curry ($(←toTerm config (depth+1) body) : $config.arrow ($config.product _ $t) _))
| .app lhs rhs => do
  `(term|
    $config.comp
      ($config.uncurry $(←toTerm config depth lhs))
      ($config.prod
        $config.id
        $(←toTerm config depth rhs)
      )
  )


def CCCTerm.IR.toString : IR → String
| .lambda t ir => s!"λᶜᶜᶜ {t} => {toString ir}"
| .showFrom ir t => s!"({toString ir} : {t})"
| .app lhs rhs => s!"({toString lhs} {toString rhs})"
| .term t => s!"`({t})"
| .arg n => s!"{n}"

instance : ToString CCCTerm.IR := ⟨CCCTerm.IR.toString⟩

def CCCTerm.IR.compile (env: List Ident) : CCCTerm.Ast → CCCTerm.IR
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

def CCCTerm.Ast.toTerm : Ast → MacroM Term
| .term t =>
  `(term| $t)
| .showFrom ast t => do
  `(term| ($(←ast.toTerm) : $t))
| .ident i =>
  `(term| $i)
| .app lhs rhs => do
  `(term| ($(←toTerm lhs) $(←toTerm rhs)))
| .lambda id type ast => do
  let ir := CCCTerm.IR.compile [] (.lambda id type ast)
  let ir ← `(term| $(←ir.toTerm Config.ContinuousHom 0))
  `(term| OmegaCompletePartialOrder.ContinuousHom.mk
    {toFun := (λ $id => $(←toTerm ast)), monotone' := ($ir).monotone'} ($ir).cont)

syntax "#generate_ccc_notation" ident stx ident : command


def CCCTerm.mkLambda (b: TSyntax `Lean.explicitBinders) (body: TSyntax `ccc_term) : MacroM (TSyntax `ccc_term) :=
  `(ccc_term| λᶜᶜᶜ $b => $body)

def CCCTerm.mkStxFromIdent (i: Ident) : TSyntax `stx := .mk <| Syntax.node .none `Lean.Parser.Syntax.cat #[i]

def CCCTerm.declIdFromIdent (i: Ident) : MacroM (TSyntax `Lean.Parser.Command.declId) := `(declId| $i)

macro_rules
| `(command| #generate_ccc_notation $cat:ident $s:stx $config) => do
  let Syntax.ident _ _ (.str Name.anonymous cat_str) _ := cat.raw | Macro.throwUnsupported
  let rule1_name : Ident := mkIdent (.str (.str .anonymous cat_str) "rule1")
  let rule2_name : Ident := mkIdent (.str (.str .anonymous cat_str) "rule2")

  let rule1_fn : Ident := mkIdent (.str (.str .anonymous cat_str) "rule1_fn")
  let rule2_fn : Ident := mkIdent (.str (.str .anonymous cat_str) "rule2_fn")
  `(


    syntax (name := $rule2_name) ($s) explicitBinders  "=>" ccc_term : ccc_term
    syntax (name := $rule1_name) ($s) explicitBinders  "=>" ccc_term : term

    @[macro $rule1_name] def $rule1_fn : Macro := λ (term: Syntax) => do
      let b : TSyntax `Lean.explicitBinders := .mk <| term.getArg 1
      let body : TSyntax `ccc_term := .mk <| term.getArg 3

      let body : TSyntax `ccc_term := .mk <| ← expandMacros body
      let list ← CCCTerm.parseBinders b
      let ast := List.foldr (λ (i, t) body => CCCTerm.Ast.lambda i t body) (←CCCTerm.Ast.parse body) list
      let ir : CCCTerm.IR := CCCTerm.IR.compile [] ast
      ir.toTerm $config 0

    @[macro $rule2_name] def $rule2_fn : Macro := λ (term: Syntax) => do
      let b : TSyntax `Lean.explicitBinders := .mk <| term.getArg 1
      let body : TSyntax `ccc_term := .mk <| term.getArg 3
      CCCTerm.mkLambda b body
  )

def foobar2 : (TSyntax `ident) := (mkIdent `x)


declare_syntax_cat ccc_term_list
syntax ccc_term "," ccc_term_list : ccc_term_list
syntax ccc_term "," ccc_term : ccc_term_list
syntax "⟨ᶜ" ccc_term_list "⟩" : ccc_term1
syntax "⟨ᵒ" ccc_term_list "⟩" : ccc_term1

macro_rules
| `(ccc_term1| ⟨ᶜ $t₁:ccc_term, $t₂:ccc_term ⟩) =>
  `(ccc_term1| OmegaCompletePartialOrder.ContinuousHom.Prod.mk($t₁, $t₂))
| `(ccc_term1| ⟨ᶜ $t₁:ccc_term, $t₂:ccc_term_list ⟩) => do
  have t₂: TSyntax `ccc_term := ← `(ccc_term| ⟨ᶜ$t₂⟩)
  `(ccc_term1| OmegaCompletePartialOrder.ContinuousHom.Prod.mk($t₁, $t₂))

#check OrderHom.curry OrderHom.id
def OrderHom.Prod.mk {α: Type u} {β: Type v} [Preorder α] [Preorder β] : α →o β →o α × β := OrderHom.curry (@OrderHom.id (α × β) _)

macro_rules
| `(ccc_term1| ⟨ᵒ $t₁:ccc_term, $t₂:ccc_term ⟩) =>
  `(ccc_term1| {OrderHom.curry OrderHom.id}($t₁, $t₂))
| `(ccc_term1| ⟨ᵒ $t₁:ccc_term, $t₂:ccc_term_list ⟩) => do
  have t₂: TSyntax `ccc_term := ← `(ccc_term| ⟨ᵒ$t₂⟩)
  `(ccc_term1| {OrderHom.curry OrderHom.id}($t₁, $t₂))

#generate_ccc_notation cont_term "λᶜ" CCCTerm.Config.ContinuousHom
#generate_ccc_notation mono_term "λᵒ" CCCTerm.Config.OrderHom


open OmegaCompletePartialOrder ContinuousHom ContinuousHom.Prod in
#check λᶜ (x : Unit × Empty) (y : _) => (λᶜ x y => fst(x))(x, y)

open OmegaCompletePartialOrder ContinuousHom ContinuousHom.Prod in
#check λᶜ f p => f(fst(p), snd(p))

open OrderHom
#check λᵒ (x : Unit × Empty) (y : _) => (λᵒ x y => fst(x))(x, y)

-- Now a small demo of it: proving that OmegaCompletePartialOrder.Cat is monoidal
namespace OmegaCompletePartialOrder.Cat
open CategoryTheory

def exp (X: Cat) : Cat ⥤ Cat where
  obj Y := of (X →𝒄 Y)

  map {Y Z} (f: Y →𝒄 Z) : (X →𝒄 Y) →𝒄 (X →𝒄 Z) :=
    λᶜ g x => f(g(x))

  map_id := by
    intro x
    simp
    rfl

  map_comp := by
    intro f g h i j
    rfl

open ContinuousHom ContinuousHom.Prod in
def adj.homEquiv (X Y Z: Cat) : (X × Y →𝒄 Z) ≃ (Y →𝒄 X →𝒄 Z) where
    toFun f := λᶜ x y => f(⟨ᶜy, x⟩)
    invFun f := λᶜ p => f(snd(p), fst(p))
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl

def adj.unit (X:Cat) : 𝟭 Cat ⟶ MonoidalCategory.tensorLeft X ⋙  X.exp where
  app Y := λᶜ (y: Y) (x:X) => ⟨ᶜx, y⟩
  naturality := by
    intro Y Z f
    rfl

open ContinuousHom ContinuousHom.Prod in
def adj.counit (X: Cat) : X.exp ⋙  MonoidalCategory.tensorLeft X ⟶  𝟭 Cat where
  app Y := λᶜ (p:X × (X →𝒄 Y)) => snd(p)(fst(p))
  naturality := by
    intro Y Z f
    rfl

open ContinuousHom ContinuousHom.Prod in
def adj (X: Cat) : MonoidalCategory.tensorLeft X ⊣ X.exp where
  homEquiv Y Z :=
    adj.homEquiv X Y Z

  unit := adj.unit X
  counit := adj.counit X
  homEquiv_unit := by aesop
  homEquiv_counit := by aesop

instance (X: Cat) : Closed X where
  rightAdj := exp X
  adj := adj X

instance : MonoidalClosed Cat where


open ContinuousHom ContinuousHom.Prod in
def π (X Y: Cat.{u}) : (Functor.const (Discrete Limits.WalkingPair)).obj (of (↑X × ↑Y)) ⟶   Limits.pair X Y where
  app
  | { as := Limits.WalkingPair.left } => λᶜ (p: X × Y) => fst(p)
  | { as := Limits.WalkingPair.right } => λᶜ (p: X × Y) => snd(p)

  naturality := by
    intro ⟨A⟩ ⟨B⟩ f
    cases A <;>
    cases B <;>
    simp at * <;>
    cases f with | up f =>
    cases f with | up f =>
    cases f


end OmegaCompletePartialOrder.Cat
