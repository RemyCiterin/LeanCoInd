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

@[simp]
def Square.rewrite_cons {α: Type u} (P: Set α) (x: α) (xs: Kahn α) :
  (x ::: xs ∈ Square P) = (x ∈ P ∧ xs ∈ Square P) := by
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

/-
  Lustre nodes are made of
  - A list of inputs variables
  - A list of locals variables
  - An expression to compute each local variable in function of the context (input+local variables)
  - An expression to compute the output of the node in function of the context (input+local variables)

  For each expression `f` we generate
  - A continuous function `f` of type I × L →𝒄 O with I := I₁ × (I₂ × ...) the type of the `n` input variables
    and L := L₁ × (L₂ × ...) the type of the `m` local variables
  - A proof `f_apply` of ∀ (i₁: I₁) ... (iₙ: Iₙ) (l₁: L₁) ... (lₘ: Lₘ), f ((i₁, ..., iₙ), (l₁, ... lₘ)) = f_expr
    with `f_expr` a simplified version of `f` (without the proof of continuity), this proof is done by reflexivity

  In addition we generate `f_fix` the fixed-point of each equations (replacing the arguments by I instead of I × L) by
  computing the fixed-point of the local variables
-/
open Lean Elab Meta in
inductive Ast : Type where
| ident : Ident → Ast
| app : Term → List Ast → Ast
| showFrom : Ast → Term → Ast
| term : Term → Ast

namespace Ast

open Lean Elab Meta

-- internal representation of lustre nodes:
-- us de Bruijn index
inductive IR where
| showFrom : IR → Term → IR
| term : Term → IR -- term antiquotation
| app : Term → List IR → IR -- sub-node
| loc : Nat → IR -- n-th local variable
| input : Nat → IR -- n-th input variable

open TSyntax.Compat in
def parseExplicitBindersAux (idents : Array Syntax) (type? : Option Syntax) (acc: List (Ident × Option Term))
  : MacroM (List (Ident × Option Term)) :=
  let rec loop (i : Nat) (acc : List (Ident × Option Term)) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let ident := (idents[i]!)[0]
      let acc := match ident.isIdent, type? with
        | true,  none      => (ident, none) :: acc
        | true,  some type => (ident, some type) :: acc
        | false, none      => (mkIdent `_, none) :: acc
        | false, some type => (mkIdent `_, some type) :: acc
      loop i acc
  loop idents.size acc

def parseBrackedBindersAux (binders : Array Syntax) (acc: List (Ident × Option Term))
  : MacroM (List (Ident × Option Term)) :=
  let rec loop (i : Nat) (acc : List (Ident × Option Term)) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let idents := (binders[i]!)[1].getArgs
      let type   := (binders[i]!)[3]
      loop i (← parseExplicitBindersAux idents (some type) acc)
  loop binders.size acc

partial def parseBinders (explicitBinders: Syntax) : MacroM (List (Ident × Option Term)) := do
  let explicitBinders := explicitBinders[0]
  if explicitBinders.getKind == ``Lean.unbracketedExplicitBinders then
    let idents   := explicitBinders[0].getArgs
    let type? := if explicitBinders[1].isNone then none else some explicitBinders[1][1]
    parseExplicitBindersAux idents type? []
  else if explicitBinders.getArgs.all (·.getKind == ``Lean.bracketedExplicitBinders) then
    parseBrackedBindersAux explicitBinders.getArgs []
  else
    Macro.throwError "unexpected explicit binder"


declare_syntax_cat tupleBinder
declare_syntax_cat tupleBinders

-- As lustre nodes use curryfication to represent their arguments,
-- binders are represented as tuples of variables
syntax binderIdent : tupleBinder
syntax binderIdent ":" term : tupleBinder
syntax "(" tupleBinder,* ")" : tupleBinders

def parseTupleBinder : TSyntax `tupleBinder → MacroM (Ident × Term)
| `(tupleBinder| _) => do
  return (mkIdent `_ , ←`(term| _))
| `(tupleBinder| $i:ident) => do
  return (i, ←`(term| _))
| `(tupleBinder| _ : $t:term) => do
  return (mkIdent `_ , t)
| `(tupleBinder| $i:ident : $t:term) => do
  return (i, t)
| _ =>
  Macro.throwError "unexpected binder"

-- parse a tuple of binders
def parseTupleBinders : TSyntax `tupleBinders → MacroM (List (Ident × Term))
| `(tupleBinders| ( $b:tupleBinder,* )) => do
  have b : Array (TSyntax `tupleBinder) := b
  List.mapM parseTupleBinder b.toList
| _ =>
  Macro.throwError "unexpected binder"

declare_syntax_cat lustre_term
declare_syntax_cat lustre_eq

syntax ident : lustre_term -- used to determine arguments and antiquotation
syntax "(" lustre_term ")" : lustre_term
syntax "(" lustre_term " : " term ")" : lustre_term
syntax "{" term "}" : lustre_term -- antiquotation

-- currified function application: the term must be of type
-- A₁ × (A₂ × ...) →𝒄 O
syntax "{" term "}" "(" lustre_term,* ")" : lustre_term -- function application
syntax ident "(" lustre_term,* ")" : lustre_term -- function application

syntax ident ":" term ":=" lustre_term : lustre_eq

-- in practice implicit type may not work because of typeclass instance inference:
-- top level metavariable instance inference generate errors
syntax ident ":=" lustre_term : lustre_eq

syntax "defnode" ident tupleBinders ":" term ":=" lustre_term "where" lustre_eq+ : command

-- proof that Ast and IR are not empty, used by partial functions
instance : Inhabited Ast := ⟨.ident (mkIdent `_)⟩
instance : Inhabited IR := ⟨.term (mkIdent `_)⟩

partial def parse_term : TSyntax `lustre_term → MacroM Ast
| `(lustre_term| $i:ident) => pure (.ident i)
| `(lustre_term| { $t:term }) => pure (.term t)
| `(lustre_term| ( $t:lustre_term )) => parse_term t
| `(lustre_term| ( $t:lustre_term : $typ:term )) => do
  return .showFrom (←parse_term t) typ
| `(lustre_term| { $t₁:term } ($t₂:lustre_term,*)) => do
  have t₂: Array (TSyntax `lustre_term) := t₂
  let t₂: List Ast ← List.mapM parse_term t₂.toList
  return .app t₁ t₂
| `(lustre_term| $t₁:ident ($t₂:lustre_term,*))  => do
  have t₂: Array (TSyntax `lustre_term) := t₂
  let t₂: List Ast ← List.mapM parse_term t₂.toList
  return .app t₁ t₂
| _ => Macro.throwError "unsupported syntax"

-- lift a lustre_term as a term by removing the proof of continuity
partial def lift_term : TSyntax `lustre_term → MacroM Term
| `(lustre_term| $i:ident) => `(term| $i)
| `(lustre_term| {$t:term}) => pure t
| `(lustre_term| ($t:lustre_term)) => lift_term t
| `(lustre_term| ($t₁:lustre_term : $t₂:term)) => do
  `(term| show $t₂ from $(←lift_term t₁))
| `(lustre_term| {$t₁: term}($t₂:lustre_term,*)) => do
  have t₂: Array (TSyntax `lustre_term) := t₂
  let t₂ : List Term ← List.mapM lift_term t₂.toList
  `($t₁ $(←go t₂))
| `(lustre_term| $t₁:ident($t₂:lustre_term,*)) => do
  have t₂: Array (TSyntax `lustre_term) := t₂
  let t₂ : List Term ← List.mapM lift_term t₂.toList
  `($t₁ $(←go t₂))
| _ => Macro.throwError "unsupported syntax"
where
  go : List Term → MacroM Term
  | x :: y :: ys => do
    `(($x, $(←go (y :: ys))))
  | [x] => pure x
  | [] =>
    Macro.throwError "unsupported syntax"

def List.last : List α → Option α
| _ :: y :: ys => last (y :: ys)
| [x] => .some x
| [] => .none

#check List.findIdx

-- replace idents by De Bruijn index
partial def compile (inputs: List Ident) (locals: List Ident) : Ast → IR
| .ident name =>
  if let .some idx := List.last (List.indexesOf name locals)
  then .loc idx
  else
    if let .some idx := List.last (List.indexesOf name inputs)
    then .input idx
    else .term name
| .app function args =>
  .app function (compile inputs locals <$> args)
| .showFrom t type =>
  .showFrom (compile inputs locals t) type
| .term t => .term t

def getPath (numArgs: Nat) : Nat → MacroM Term
| n+1 => do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      $(←getPath (numArgs-1) n)
      OmegaCompletePartialOrder.ContinuousHom.Prod.snd
  )
| 0 =>
  if numArgs = 1
  then  `(term| OmegaCompletePartialOrder.ContinuousHom.id)
  else `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.fst)

-- return a function of type Inputs × Locals →𝒄 argType
def getInput (arg: Nat) (numInputs: Nat) : MacroM Term := do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      $(←getPath numInputs arg)
      OmegaCompletePartialOrder.ContinuousHom.Prod.fst
  )

-- return a function of type Inputs × Locals →𝒄 argType
def getLoc (arg: Nat) (numLocals: Nat) : MacroM Term := do
  `(term|
    OmegaCompletePartialOrder.ContinuousHom.comp
      $(←getPath numLocals arg)
      OmegaCompletePartialOrder.ContinuousHom.Prod.snd
  )

#print IR

#check ContinuousHom.Prod.curry
#check ContinuousHom.Prod.prod
#check Nat.foldM
#check List.foldlM


-- like prod but of arrity n: return a function of type `α →𝒄 T₁ × ... Tₙ` from a list of functions
-- of type `α →𝒄 Tᵢ`
def prodNarith : List Term → MacroM Term
| [] => Macro.throwError "empty function application"
| [t] => pure t
| x :: xs => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.prod $x $(←prodNarith xs))

partial def IR.toTerm (numInputs numLocals: Nat) : IR → MacroM Term
| .showFrom ir t => do `(term| (show _ × _ →𝒄 Kahn $t from $(←ir.toTerm numInputs numLocals)))
| .input n => getInput n numInputs
| .loc n => getLoc n numLocals
| .term t => `(term| OmegaCompletePartialOrder.ContinuousHom.const $t)
| .app function [] => do
  `(term| OmegaCompletePartialOrder.ContinuousHom.const $function)
| .app function args => do
  -- A list of terms of type I × L →𝒄 Tᵢ
  let args ← List.mapM (toTerm numInputs numLocals) args
  -- function is of type T₀ × ... × Tₙ →𝒄 T
  -- args_fun is of type I × L →𝒄 T₀ × ... × Tₙ
  let args_fun ← genArgs args

  -- so function.comp args_fun has type I × L →𝒄 T
  `(term| OmegaCompletePartialOrder.ContinuousHom.comp $function $args_fun)
where
  genArgs : List Term → MacroM Term
  | [] => Macro.throwError "empty function application"
  | [t] => pure t
  | x :: xs => do
    `(term| OmegaCompletePartialOrder.ContinuousHom.Prod.prod $x $(←genArgs xs))

syntax "λˡᵘˢᵗʳᵉ" explicitBinders "=>" explicitBinders "=>" lustre_term : term

-- defcont foo (i₁: I₁) ... (iₙ: Iₙ) => (l₁: L₁) ... (lₙ: Lₙ) : type := t generate two functions:
-- - A function foo of type, all the type must be explicit because lean cannot assume that
--   a metavariable in a declaration is an instance of the OmegaCompletePartialOrder typeclass
syntax "defcont" ident tupleBinders tupleBinders ":" term ":=" lustre_term : command

def prodOfList : List Term → MacroM Term
| [] => Macro.throwError ""
| [x] => pure x
| x :: xs => do
  `($x × $(←prodOfList xs))

macro_rules
| `(term| λˡᵘˢᵗʳᵉ $b₁:explicitBinders => $b₂:explicitBinders => $body:lustre_term) => do
  have body : TSyntax `lustre_term := .mk <| ← expandMacros body
  let l₁ ← parseBinders b₁
  let l₂ ← parseBinders b₂
  let ast ← parse_term body
  let ir := ast.compile (Prod.fst <$> l₁) (Prod.fst <$> l₂)
  let empty : Term ← `(term| _)
  let l₁_type := (λ (_, t) =>
    match t with
    | .some v => v
    | .none => empty
  ) <$> l₁
  let l₂_type := (λ (_, t) =>
    match t with
    | .some v => v
    | .none => empty
  ) <$> l₂
  `(term| show $(←prodOfList l₁_type) × $(←prodOfList l₂_type) →𝒄 _ from $(←ir.toTerm l₁.length l₂.length))

partial def mkProduct : List Ident → MacroM Term
| x :: y :: ys => do `(term|($x, $(←mkProduct (y :: ys))))
| [x] => pure x
| [] => `(term|())

partial def mkForall : List Ident → List Term → Term → MacroM Term
| x :: xs, y :: ys, out => do
  match y with
  | `(term| _) =>
    `(∀ $x, $(←mkForall xs ys out))
  | _ =>
    `(∀ ($x : $y), $(←mkForall xs ys out))
| _, _, t => pure t

structure Binders where
  idents : List Ident
  types  : List Term

def Binders.parse : TSyntax `tupleBinders → MacroM Binders := λ b => do
  let list ← parseTupleBinders b
  return ⟨Prod.fst <$> list, Prod.snd <$> list⟩

structure Equations where
  idents : List Ident
  types : List Term
  eqs : List (TSyntax `lustre_term)

def Equations.binders (eqs: Equations) : Binders where
  idents := eqs.idents
  types := eqs.types

def parseEq : TSyntax `lustre_eq → MacroM (Ident × Term × TSyntax `lustre_term)
| `(lustre_eq| $i:ident : $t:term := $l:lustre_term) =>
  pure (i, t, l)
| `(lustre_eq| $i:ident := $l:lustre_term) => do
  return (i, ←`(term| _), l)
| _ => Macro.throwUnsupported

def Equations.parse : List (TSyntax `lustre_eq) → MacroM Equations := λ eqs => do
  let eqs ← List.mapM parseEq eqs
  let idents := (λ ⟨id, _, _⟩ => id) <$> eqs
  let types := (λ ⟨_, t, _⟩ => t) <$> eqs
  let eqs := (λ ⟨_, _, eq⟩ => eq) <$> eqs
  return ⟨idents, types, eqs⟩

def Ident.addSuffix (i: Ident) (suffix: String) : MacroM Ident := do
  let Syntax.ident _ _ (.str name last_string) _ := i.raw | Macro.throwUnsupported
  return mkIdent (.str name (last_string ++ suffix))

def Ident.addPrefix (i: Ident) (pref: String) : MacroM Ident := do
  let Syntax.ident _ _ (.str name last_string) _ := i.raw | Macro.throwUnsupported
  return mkIdent (.str name (pref ++ last_string))

def Ident.addNamespace (i: Ident) (str: String) : MacroM Ident := do
  let Syntax.ident _ _ name _ := i.raw | Macro.throwUnsupported
  return mkIdent (.str name str)

macro_rules
| `(command| defcont $name_ident:ident $inputs:tupleBinders $locals:tupleBinders : $O:term := $body:lustre_term) => do
  have body : TSyntax `lustre_term := .mk <| ← expandMacros body
  let name_apply ← Ident.addSuffix name_ident "_apply"
  let inputs ← Binders.parse inputs
  let locals ← Binders.parse locals
  let ast ← parse_term body
  let ir := ast.compile inputs.idents locals.idents
  let I ← prodOfList inputs.types
  let L ← prodOfList locals.types
  let i ← mkProduct inputs.idents
  let l ← mkProduct locals.idents
  let thm_body : Term ← `($name_ident ($i, $l) = $(←lift_term body))
  let thm ← mkForall inputs.idents inputs.types (←mkForall locals.idents locals.types thm_body)
  `(
    def $name_ident : $I × $L →𝒄 $O :=
      $(←ir.toTerm inputs.idents.length locals.idents.length)
    @[simp] def $name_apply : $thm := by intros; rfl
  )

open ContinuousHom.Kahn Kahn in
defcont foo (x : Kahn Int, y: Kahn Int) (z: Kahn Int, t: Kahn Int) : Kahn Int :=
  fby({const 0}, x)

#print foo
#check foo_apply


-- macro_rules
-- | `(command| defnode $name_ident:ident $b₁:explicitBinders : $O := $out:lustre_term where $eqs:lustre_eq*) => do
--   let Syntax.ident _ _ name _ := name_ident.raw | Macro.throwUnsupported
--   let name_out := mkIdent (.str name "out")
--   let name_eqs := mkIdent (.str name "eqs")
--   let name_fix := mkIdent (.str name "fix")
--   let name_ind := mkIdent (.str name "ind")
--   let name_fold := mkIdent (.str name "unfold")
--   let name_post := mkIdent (.str name "post")
--   let name_eval := mkIdent (.str name "eval")
--
--   let empty : Term ← `(term| _)
--
--   have inputs := (λ (i, t) => (i, Option.getD t empty)) <$> (← parseBinders b₁)
--   let locals ← List.mapM parseEq eqs.toList
--
--   have inputs_name := (λ (name, _) => name) <$> inputs
--   have inputs_type := (λ (_, type) => type) <$> inputs
--
--   have locals_name := (λ (name, _, _) => name) <$> locals
--   have locals_type := (λ (_, type, _) => type) <$> locals
--   have locals_term := (λ (_, _, expr) => expr) <$> locals
--
--   let I ← prodOfList inputs_type
--   let L ← prodOfList locals_type
--
--   have toTerm ir := IR.toTerm inputs_type.length locals_type.length ir
--
--   have output_ir := (←parse_term out).compile inputs_name locals_name
--   let output_term ← `(show $I × $L →𝒄 _ from $(←toTerm output_ir))
--
--   let locals_ir ←
--     List.mapM (λ eq => do
--       return (←parse_term eq).compile inputs_name locals_name
--     ) locals_term
--
--   let locals_term ←
--     List.mapM (λ ir => do
--       `(show $I × $L →𝒄 _ from $(←toTerm ir))
--     ) locals_ir
--
--   `(
--     def $name_out : $I × $L →𝒄 $O := $output_term
--     def $name_eqs : $I × $L →𝒄 $L := $(←prodNarith locals_term)
--     noncomputable def $name_fix : $I →𝒄 $L :=
--       OmegaCompletePartialOrder.ContinuousHom.comp
--         OmegaCompletePartialOrder.ContinuousHom.fix
--         (OmegaCompletePartialOrder.ContinuousHom.Prod.curry $name_eqs)
--
--     def $name_fold (i: $I) :
--       $name_fix i = $name_eqs (i, $name_fix i) :=
--       OmegaCompletePartialOrder.ContinuousHom.fix.unfold
--         (OmegaCompletePartialOrder.ContinuousHom.Prod.curry $name_eqs i)
--
--
--     noncomputable def $name_eval : $I →𝒄 $O :=
--       OmegaCompletePartialOrder.ContinuousHom.comp
--         $name_out
--         (OmegaCompletePartialOrder.ContinuousHom.Prod.prod
--           OmegaCompletePartialOrder.ContinuousHom.id
--           $name_fix)
--
--     -- prove that a property is an invariant
--     def $name_ind (Pre: Admissible $I) (Inv: Admissible $L) :
--       (∀ i l, i ∈ Pre → l ∈ Inv → $name_eqs (i, l) ∈ Inv) → ∀ (i: $I), i ∈ Pre → $name_fix i ∈ Inv :=
--       OmegaCompletePartialOrder.Admissible.NodeFix_thm
--         (OmegaCompletePartialOrder.ContinuousHom.Prod.curry $name_eqs)
--         Pre Inv
--
--     def $name_post (Pre: Admissible $I) (Inv: Admissible $L) (Post: Admissible $O) :
--       (∀ i l, i ∈ Pre → l ∈ Inv → $name_out (i, l) ∈ Post) → (∀ i, i ∈ Pre → $name_fix i ∈ Inv) →
--       ∀ i, i ∈ Pre → $name_eval i ∈ Post :=
--       λ h₁ h₂ i h₃ => h₁ i ($name_fix i) h₃ (h₂ i h₃)
--   )

defnode foo (i₁: Kahn ℕ) : Kahn ℕ := l₁
  where
    l₁ : Kahn ℕ := {ContinuousHom.Kahn.fby}({Kahn.const 1}, l₁)

-- from I × L to O
#print foo.out

-- from I × L to L
#print foo.eqs

-- from I to L
#print foo.fix

-- from I to O
#print foo.eval

-- induction principe
#check foo.ind

-- extract a post condition from an invariant
#check foo.post

-- unfold the fix function
#check foo.unfold

end Ast


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
  λᶜ x y => {ContinuousHom.Kahn.map (λ (x, y) => x+y)}(ContinuousHom.Kahn.tup(x, y))

def proj.i : Str I →𝒄 Kahn (I.type I.var.i) := proj .i

#check ContinuousHom.Kahn.fby

def Eqs : (l: L.var) → Str I →𝒄 Str L →𝒄 Kahn (L.type l)
| .x => λᶜ i l => ContinuousHom.Kahn.add(proj.i(i), {ContinuousHom.Kahn.fby (Kahn.const 0)}({proj L.var.x}(l)))
| .y => λᶜ i l => {proj L.var.z}(l)
| .z => λᶜ i l => {proj L.var.y}(l)

def Out : (v: O.var) → Str I →𝒄 Str L →𝒄 Kahn (O.type v)
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
      simp [eqs.apply, Eqs]
      simp [proj.i]
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
          rw [Kahn.const.unfold]
          simp? [spec.Local]
          constructor
          · simp only [spec.Input, Square.rewrite_cons] at h₁
            exact h₁.left
          · refinment_type
        | cons y ys =>
          rw [Kahn.const.unfold]
          simp [spec.Local]
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
