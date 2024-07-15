import Lean.PrettyPrinter.Delaborator
import CoInd.Std.DelabRule
import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils
import CoInd.Stream.LTLBase


import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq


open Lean Lean.Macro Lean.Expr Lean.Meta Qq Elab.Tactic Elab
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

#print Expr

@[match_pattern] def nameAnnotation := `name
@[match_pattern] def uniqAnnotation := `uniq

def parseName? : Expr → Option (Name × Name × Expr)
  | .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ e => do
    some (name, uniq, e)
  | _ => none

def mkNameAnnotation (name uniq : Name) (e : Expr) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ e

inductive Hyps {u: Level} {prop: Q(Type u)} (ltl: Q(LTL $prop)) : Q($prop) → Type where
| and {P Q e: Q($prop)} (_: $e =Q tprop($P ∧ $Q)) (lhs: Hyps ltl P) (rhs: Hyps ltl Q) : Hyps ltl e
| hyp (e: Q($prop)) (name uniq: Name) : Hyps ltl e
| nul (_: $e =Q tprop(⊤)) : Hyps ltl e

partial def Hyps.toExpr {u: Level} {prop: Q(Type u)} {ltl: Q(LTL $prop)} {e:Q($prop)} : Hyps ltl e → Q($prop)
| .and _ lhs rhs => q(tprop($(toExpr lhs) ∧ $(toExpr rhs)))
| .hyp e name uniq => mkNameAnnotation name uniq e
| .nul _ => q(tprop(⊤))

abbrev LTL.Entails' (PROP: Type u) [LTL PROP] (P Q: PROP) : Prop := P ⊢ Q

-- A LTL goal is a proof goal of the form `P ⊢ Q`, we maintain
-- the expression of Q (as "e") and P (as "goal") in the form of a
-- list of hypothesis such that P is the big-and of "hyps"
structure LTLGoal where
  u: Level
  prop: Q(Type u)
  ltl: Q(LTL $prop)
  e : Q($prop)
  hyps : Hyps ltl e
  goal : Q($prop)

def LTLGoal.toExpr : LTLGoal → Q(Prop)
| ⟨u, prop, ltl, e, hyps, goal⟩ =>
  q(LTL.Entails' _ $(hyps.toExpr) $goal)

-- def appM? (e : Expr) (fName : Name) : Option <| Array Expr :=
--   if e.isAppOf fName then
--     e.getAppArgs
--   else
--     none

#print isAppOf
#print getAppFn

#print Expr

partial def parseLTLHyps {u: Level} {prop: Q(Type u)} (ltl: Q(LTL $prop)) : ∀ e: Q($prop), MetaM (Option (Hyps ltl e))
| .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ _ => do
  return .some <| .hyp _ name uniq
| ~q(tprop(⊤)) => do
  return .some <| .nul ⟨⟩
| ~q(tprop($P ∧ $Q)) => do
  let lhs? ← parseLTLHyps ltl P
  let rhs? ← parseLTLHyps ltl Q
  return do
    let lhs ← lhs?
    let rhs ← rhs?
    return .and ⟨⟩ lhs rhs
-- | e => return .some <| .hyp _ `foo `foo
| _ => return .none

partial def parseLTLGoal : Q(Prop) → MetaM (Option LTLGoal)
| ~q(@LTL.Entails' $prop $ltl $p $q) => do
  -- infer the univer of $prop
  let .sort (.succ u) ← whnf (← inferType prop) | throwError "The type of an instance of LTL must be `Type u` for some `u`"
  have prop : Q(Type u) := prop
  have ltl  : Q(LTL $prop) := ltl
  have p    : Q($prop) := p
  have q    : Q($prop) := q

  -- parse hypothesis
  let hyps ← parseLTLHyps ltl p
  return (λ h => LTLGoal.mk u prop ltl p h q) <$> hyps
| _ => return .none

syntax ltlHyp := ident " : " term

syntax ltlGoalStx := ppDedent(ppLine ltlHyp)* ppDedent(ppLine "⊢ " term)

#check delab
#print Delab
#print DelabM
#print PrettyPrinter.Delaborator.Context

#check unpackTprop

#check withAppArg

@[delab app.LTL.Entails']
def delabLTLEntails' : Delab := do
  let expr ← instantiateMVars <| ← getExpr
  let .some goal ← parseLTLGoal expr | failure

  let (_, hyps) ← delabHypotheses goal.hyps ({}, #[])
  let goal ← unpackTprop (← Lean.PrettyPrinter.delabCore goal.goal default delab).fst -- (← delab goal)

  -- build syntax
  return ⟨← `(ltlGoalStx| $hyps.reverse* ⊢ $goal:term)⟩
where
delabHypotheses {u} {prop bi s} (hyps : @Hyps u prop bi s)
    (acc : NameMap Nat × Array (TSyntax ``ltlHyp)) :
    DelabM (NameMap Nat × Array (TSyntax ``ltlHyp)) := do
  match hyps with
  | .nul _ => pure acc
  | .hyp _ name _ =>
    let mut (map, acc) := acc
    let (idx, name') ← if let some idx := map.find? name then
      pure (idx + 1, name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
    else
      pure (0, name)
    let stx ← `(ltlHyp| $(mkIdent name') : $(← unpackTprop (← Lean.PrettyPrinter.delabCore s default delab).fst))
    pure (map.insert name idx, acc.push stx)
  | .and _ lhs rhs => delabHypotheses lhs (← delabHypotheses rhs acc)

#check LTL.mp
#check LTL.imp_elim
#check LTL.imp_intro

#check LTL.top_and

def tstart_thm {PROP: Type u} [LTL PROP] {P Q: PROP} :
  LTL.Entails' PROP tprop(⊤) tprop(P → Q) → P ⊢ Q := by
  unfold LTL.Entails'
  intro h₁
  rw [←@LTL.top_and _ _ P]
  apply LTL.imp_elim
  assumption

macro "tstart" : tactic => `(tactic| apply tstart_thm)

#check Hyps.and
#check Hyps.hyp

def getFreshName : TSyntax ``binderIdent → CoreM (Name × Syntax)
| `(binderIdent| $name:ident) => pure (name.getId, name)
| stx => return (← mkFreshUserName `x, stx)

#check LTLGoal.mk
#check withLocalDeclDQ
#check synthInstanceQ
#check mkFreshExprMVarQ

#check LTL.imp_intro

#print Hyps

#check LTLBase.Entails.rfl
#check LTL.and_elim_r

-- search in the hypothesis if a name exist in a set of hypothesis `P`, if true return
-- the property `Q` and a proof of `P ⊢ Q`
def Hyps.search {u: Level} {prop: Q(Type u)} {ltl: Q(LTL $prop)} {P: Q($prop)}
  (hyps: Hyps ltl P) (name: Name) : Option <| (Q:Q($prop)) × Q($P ⊢ $Q) :=
  match hyps with
  | .and _ lhs rhs =>
    match (lhs.search name, rhs.search name) with
    | (_, .some ⟨R, h⟩) =>
      .some ⟨R, q(by simp only; apply LTL.and_elim_r.trans; assumption)⟩
    | (.some ⟨R, h⟩, .none) =>
      .some ⟨R, q(by simp only; apply LTL.and_elim_l.trans; assumption)⟩
    | (.none, .none) =>
      .none
  | .hyp e n uniq =>
    if n == name then
      .some ⟨e, q(LTLBase.Entails.rfl)⟩
    else
        .none
  | .nul _ => .none



