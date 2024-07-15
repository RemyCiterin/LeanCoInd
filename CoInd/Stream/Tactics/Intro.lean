import Lean.PrettyPrinter.Delaborator
import CoInd.Std.DelabRule
import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils
import CoInd.Stream.LTLBase
import CoInd.Stream.Expr

import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq


open Lean Lean.Macro Lean.Expr Lean.Meta Qq Elab.Tactic Elab
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

declare_syntax_cat tcasesPat
syntax tcasesPatAlts := sepBy1(tcasesPat, " | ")
syntax binderIdent : tcasesPat
syntax "⟨" tcasesPatAlts,* "⟩" : tcasesPat
syntax "(" tcasesPatAlts ")" : tcasesPat
syntax "⌜" tcasesPat "⌝" : tcasesPat

inductive tCasesPat
| one (name: TSyntax ``binderIdent)
--| clear
| conjunction (args: List tCasesPat)
| disjunction (args: List tCasesPat)
| pure (pat: tCasesPat)
deriving Repr, Inhabited

-- parse a pattern and return an inductive version of it
partial def tCasesPat.parse (pat: TSyntax `tcasesPat) : MacroM tCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
  where
    go : TSyntax `tcasesPat → Option tCasesPat
    | `(tcasesPat| $name:binderIdent) => .some <| .one name
    | `(tcasesPat| ⟨$[$args],*⟩) => .conjunction <$> args.toList.mapM goAlts
    | `(tcasesPat| ⌜$pat⌝) => go pat |>.map .pure
    | `(tcasesPat| ($pat)) => goAlts pat
    | _ => .none

    goAlts : TSyntax ``tcasesPatAlts → Option tCasesPat
    | `(tcasesPatAlts| $args|*) =>
      match args.getElems with
      | #[arg] => go arg
      | args => .disjunction <$> args.toList.mapM go
    | _ => .none


abbrev temporal_tactic_core :=
  (u: Level) → (prop: Q(Type u)) → (ltl: Q(LTL $prop)) →
  (∀ P Q: Q($prop), Hyps ltl P → MetaM Q($P ⊢ $Q)) → (P Q: Q($prop)) →
  Hyps ltl P → MetaM Q($P ⊢ $Q)

#check LTL.and_symm

def LTL.introCore.aux₁ {prop: Type u} [LTL prop] (P Q R S: prop) :
  (P ∧ Q ⊢ S) → (P ∧ R ⊢ S) → (P ⊢ Q ∨ R → S) := by
    intro h₁ h₂
    have h₁ := imp_intro (and_symm.trans h₁)
    have h₂ := imp_intro (and_symm.trans h₂)
    apply imp_intro
    apply and_symm.trans
    apply imp_elim
    apply or_elim
    <;> assumption

#check LTL.and_assoc

def LTL.introCore.aux₂ {prop: Type u} [LTL prop] (P Q R S: prop) :
  (P ⊢ Q → R → S) → P ⊢ Q ∧ R → S := by
  intro h
  have h := and_assoc.2.trans <| LTL.imp_elim (LTL.imp_elim h)
  apply imp_intro
  assumption

partial def introCore (names: List tCasesPat) (u: Level) (prop: Q(Type u))
  (ltl: Q(LTL $prop)) (k: ∀ P Q: Q($prop), Hyps ltl P → MetaM Q($P ⊢ $Q))
  (P Q: Q($prop)) (hyps: Hyps ltl P) : MetaM Q($P ⊢ $Q) := do
  match Q, names with
  | _, [] => k P Q hyps
  | ~q(tprop($R → $S)), .one name :: names =>
    let (freshName, _) ← getFreshName name
    let freshGoal ← introCore names u prop ltl k q(tprop($P ∧ $R)) S (.and ⟨⟩ hyps (.hyp R freshName freshName))
    return q(@LTL.imp_intro $prop $ltl $P $R $S $freshGoal)

  | _, .conjunction conj :: names =>
    goConj conj names P Q hyps

  | _, .disjunction disj :: names =>
    goDisj disj names P Q hyps
where
  goDisj : List tCasesPat → List tCasesPat → (P Q: Q($prop)) → Hyps ltl P → MetaM Q($P ⊢ $Q)
  | disj, names, P, Q, hyps => do
    match Q, disj with
    | _, [] => introCore names u prop ltl k P Q hyps

    | _, [pat₁] =>
      introCore (pat₁ :: names) u prop ltl k P Q hyps

    | ~q(tprop($R₁ ∨ $R₂ → $S)), pat₁ :: pat₂ =>
      let h₁ ← introCore (pat₁ :: names) u prop ltl k q(tprop($P)) q(tprop($R₁ → $S)) hyps
      let h₂ ← goDisj pat₂ names q(tprop($P)) q(tprop($R₂ → $S)) hyps
      return q(LTL.introCore.aux₁ $P $R₁ $R₂ $S (LTL.imp_elim $h₁) (LTL.imp_elim $h₂))

  goConj : List tCasesPat → List tCasesPat → (P Q: Q($prop)) → Hyps ltl P → MetaM Q($P ⊢ $Q)
  | conj, names, P, Q, hyps => do
    match Q, conj with
    | _, [] => introCore names u prop ltl k P Q hyps

    | ~q(tprop($R₁ → $S)), [pat₁] =>
      introCore (pat₁ :: names) u prop ltl k P q(tprop($R₁ → $S)) hyps

    | ~q(tprop($R₁ ∧ $R₂ → $S)), pat₁ :: pat₂ =>
      let h ← introCore (pat₁ :: .conjunction pat₂ :: names) u prop ltl k q(tprop($P)) q(tprop($R₁ → $R₂ → $S)) hyps
      return q(LTL.introCore.aux₂ $P $R₁ $R₂ $S $h)

#check LTL.or_elim

#check getMainGoal
#check MVarId.withContext

elab "tintro" pats:(colGt tcasesPat)* : tactic => do
  -- parse syntax
  -- let pats ← liftMacroM pats -- <| pats.mapM <| iCasesPat.parse

  let mvar ← getMainGoal
  let .some ⟨u, prop, ltl, P, hyps, Q⟩ ← parseLTLGoal (← inferType <| .mvar mvar) | throwError ""
  -- let (mvar, ⟨ u, prop, ltl, hyps, goal ⟩) ← tstart (← getMainGoal)
  mvar.withContext do

    -- process patterns
    let goals ← IO.mkRef #[]
    let pats ← liftMacroM <| pats.toList.mapM <| tCasesPat.parse
    let pf ← introCore pats u prop ltl (fun P goal hyps => do
      let m : Q($P ⊢ $goal) ← mkFreshExprMVarQ <|
        LTLGoal.toExpr { u, prop, ltl, hyps, goal }
      goals.modify (·.push m.mvarId!)
      pure m) P Q hyps

    mvar.assign pf
    replaceMainGoal (← goals.get).toList
