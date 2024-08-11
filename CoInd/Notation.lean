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

def ContTerm.mkArg (depth: ℕ) : Nat → MacroM (TSyntax `term)
| 0 => do
  -- at depth 1 the only free variable has value 0
  if depth = 1
  then `(term| OmegaCompletePartialOrder.ContinuousHom.id)
  else `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.snd)
| n+1 => do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      $(←mkArg (depth-1) n) OmegaCompletePartialOrder.ContinuousHom.Prod.fst)

def ContTerm.IR.toTerm (depth: ℕ) : IR → MacroM Term
| .arg n => mkArg depth n
| .showFrom ir t => do
  `(term| ($(←toTerm depth ir) : _ →𝒄 $t))
| .term t => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.const $t)
| .lambda .none body => do
  if depth = 0
  then `(term| $(←toTerm (depth+1) body))
  else `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.curry $(←toTerm (depth+1) body))
| .lambda (.some t) body => do
  if depth = 0
  then `(term| ($(←toTerm (depth+1) body) : $t →𝒄 _))
  else `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.curry ($(←toTerm (depth+1) body) : _ × $t →𝒄 _))
| .app lhs rhs => do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      (OmegaCompletePartialOrder.ContinuousHom.Prod.curry.symm $(←toTerm depth lhs))
      (OmegaCompletePartialOrder.ContinuousHom.Prod.prod
        OmegaCompletePartialOrder.ContinuousHom.id
        $(←toTerm depth rhs)
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
def ContTerm.IR.compile (env: List Ident) : ContTerm.Ast → ContTerm.IR
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

#check Lean.expandMacros
#print TSyntax

#print ContTerm.Ast

def ContTerm.Ast.toTerm : Ast → MacroM Term
| .term t =>
  `(term| $t)
| .showFrom ast t => do
  `(term| ($(←ast.toTerm) : $t))
| .ident i =>
  `(term| $i)
| .app lhs rhs => do
  `(term| ($(←toTerm lhs) $(←toTerm rhs)))
| .lambda id type ast => do
  let ir := ContTerm.IR.compile [] (.lambda id type ast)
  let ir ← `(term| $(←ir.toTerm 0))
  `(term| OmegaCompletePartialOrder.ContinuousHom.mk
    {toFun := (λ $id => $(←toTerm ast)), monotone' := ($ir).monotone'} ($ir).cont)

#check OmegaCompletePartialOrder.ContinuousHom.mk

macro_rules
| `(term| λᶜ $b:explicitBinders => $body:cont_term) => do
  let body : TSyntax `cont_term := .mk <| ← expandMacros body
  let list ← ContTerm.parseBinders b
  let ast := List.foldr (λ (i, t) body => ContTerm.Ast.lambda i t body) (←ContTerm.Ast.parse body) list
  let ir : ContTerm.IR := ContTerm.IR.compile [] ast
  ir.toTerm 0


declare_syntax_cat cont_term_list
syntax cont_term "," cont_term_list : cont_term_list
syntax cont_term "," cont_term : cont_term_list
syntax "⟨" cont_term_list "⟩" : cont_term1

macro_rules
| `(cont_term1| ⟨ $t₁:cont_term, $t₂:cont_term ⟩) =>
  `(cont_term1| OmegaCompletePartialOrder.ContinuousHom.Prod.mk($t₁, $t₂))
| `(cont_term1| ⟨ $t₁:cont_term, $t₂:cont_term_list ⟩) => do
  have t₂: TSyntax `cont_term := ← `(cont_term| ⟨$t₂⟩)
  `(cont_term1| OmegaCompletePartialOrder.ContinuousHom.Prod.mk($t₁, $t₂))


open OmegaCompletePartialOrder ContinuousHom ContinuousHom.Prod in
#check λᶜ (x : Unit ⊕ Empty) (y : _) => fst(⟨x, y, y⟩)


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
    toFun f := λᶜ x y => f(⟨y, x⟩)
    invFun f := λᶜ p => f(snd(p), fst(p))
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl

#print NatTrans

def adj.unit (X:Cat) : 𝟭 Cat ⟶ MonoidalCategory.tensorLeft X ⋙  X.exp where
  app Y := λᶜ (y: Y) (x:X) => ⟨x, y⟩
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


--instance (X Y:Cat.{u}) : Limits.HasBinaryProduct X Y where
--  exists_limit := ⟨⟨of (X × Y), π X Y⟩, ⟨λ ⟨pt, ⟨pi, _⟩⟩ => by
--    simp [Functor.const, Discrete, Limits.pair] at *
--    specialize pi {as := .left}
--    simp [Limits.pair, Functor.const, Discrete] at *
--  , by
--    sorry
--  , by
--    sorry
--  ⟩⟩

end OmegaCompletePartialOrder.Cat
