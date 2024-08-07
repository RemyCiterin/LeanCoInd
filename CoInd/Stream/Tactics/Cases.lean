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

-- def LTL.introCore.aux₁ {prop: Type u} [LTL prop] (P Q R S: prop) :
--   (P ∧ Q ⊢ S) → (P ∧ R ⊢ S) → (P ⊢ Q ∨ R → S) := by
--     intro h₁ h₂
--     have h₁ := imp_intro (and_symm.trans h₁)
--     have h₂ := imp_intro (and_symm.trans h₂)
--     apply imp_intro
--     apply and_symm.trans
--     apply imp_elim
--     apply or_elim
--     <;> assumption
--
-- #check LTL.and_assoc
--
-- def LTL.introCore.aux₂ {prop: Type u} [LTL prop] (P Q R S: prop) :
--   (P ⊢ Q → R → S) → P ⊢ Q ∧ R → S := by
--   intro h
--   have h := and_assoc.2.trans <| LTL.imp_elim (LTL.imp_elim h)
--   apply imp_intro
--   assumption
--
-- partial def introCore (names: List tCasesPat) (u: Level) (prop: Q(Type u))
--   (ltl: Q(LTL $prop)) (k: ∀ P Q: Q($prop), Hyps ltl P → MetaM Q($P ⊢ $Q))
--   (P Q: Q($prop)) (hyps: Hyps ltl P) : MetaM Q($P ⊢ $Q) := do
--   match Q, names with
--   | _, [] => k P Q hyps
--   | ~q(tprop($R → $S)), .one name :: names =>
--     let (freshName, _) ← getFreshName name
--     let freshGoal ← introCore names u prop ltl k q(tprop($P ∧ $R)) S (.and ⟨⟩ hyps (.hyp R freshName freshName))
--     return q(@LTL.imp_intro $prop $ltl $P $R $S $freshGoal)
--
--   | _, .conjunction conj :: names =>
--     goConj conj names P Q hyps
--
--   | _, .disjunction disj :: names =>
--     goDisj disj names P Q hyps
-- where
--   goDisj : List tCasesPat → List tCasesPat → (P Q: Q($prop)) → Hyps ltl P → MetaM Q($P ⊢ $Q)
--   | disj, names, P, Q, hyps => do
--     match Q, disj with
--     | _, [] => introCore names u prop ltl k P Q hyps
--
--     | _, [pat₁] =>
--       introCore (pat₁ :: names) u prop ltl k P Q hyps
--
--     | ~q(tprop($R₁ ∨ $R₂ → $S)), pat₁ :: pat₂ =>
--       let h₁ ← introCore (pat₁ :: names) u prop ltl k q(tprop($P)) q(tprop($R₁ → $S)) hyps
--       let h₂ ← goDisj pat₂ names q(tprop($P)) q(tprop($R₂ → $S)) hyps
--       return q(LTL.introCore.aux₁ $P $R₁ $R₂ $S (LTL.imp_elim $h₁) (LTL.imp_elim $h₂))
--
--   goConj : List tCasesPat → List tCasesPat → (P Q: Q($prop)) → Hyps ltl P → MetaM Q($P ⊢ $Q)
--   | conj, names, P, Q, hyps => do
--     match Q, conj with
--     | _, [] => introCore names u prop ltl k P Q hyps
--
--     | ~q(tprop($R₁ → $S)), [pat₁] =>
--       introCore (pat₁ :: names) u prop ltl k P q(tprop($R₁ → $S)) hyps
--
--     | ~q(tprop($R₁ ∧ $R₂ → $S)), pat₁ :: pat₂ =>
--       let h ← introCore (pat₁ :: .conjunction pat₂ :: names) u prop ltl k q(tprop($P)) q(tprop($R₁ → $R₂ → $S)) hyps
--       return q(LTL.introCore.aux₂ $P $R₁ $R₂ $S $h)

--partial def casesCore (pat: tCasesPat) (u: Level) (prop: Q(Type u))
--  (ltl: Q(LTL $prop)) (k: ∀ P Q: Q($prop), Hyps ltl P → MetaM Q($P ⊢ $Q))
--  (P Q: Q($prop)) (hyps: Hyps ltl P) (R: Q($prop)) (h₁:Q($P ⊢ R)) : MetaM Q($P ⊢ $Q) := do
--  match R, pat with
--  | _, .one name =>
--    let (freshName, _) ← getFreshName name
--    k q(tprop($P ∧ $R)) Q (.and ⟨⟩ hyps (.hyp R freshName freshName))
--  | ~q(tprop($A ∧ B)), .conjunction (x :: xs) =>
--    let h ← casesCore (.conjunction xs) u prop ltl k q(tprop($P ∧ $A)) Q ()

-- take a list of ident and revert them
-- if `h: P`, and the hypothesis is of the form `(R := ... ∧ P ∧ ...) ⊢ Q`
--def revertCore (names: List Ident) (u: Level) (prop: Q(Type u))
--  (ltl: Q(LTL $prop)) (k: ∀ P Q: Q($prop), Hyps ltl P → MetaM Q($P ⊢ $Q))
--  (P Q: Q($prop)) (hyps: Hyps ltl P) : MetaM Q($P ⊢ $Q)

#check Subtype

#check Hyps.hyp
#check Hyps.and

#check LTL.bientails_iff_eq
#check LTL.and_assoc
#check LTL.and_comm
#check LTL.and_symm

structure Hyps.revert.Result {u: Level} {prop: Q(Type u)} (ltl: Q(LTL $prop)) (P: Q($prop)) where
  response : Q($prop)
  rest : Q($prop)
  hyps : Hyps ltl rest
  rel : Q($P = tprop($rest ∧ $response))

def Hyps.revert {u: Level} {prop: Q(Type u)} {ltl: Q(LTL $prop)} {P: Q($prop)}
  (hyps: Hyps ltl P) (name: Name) : Option <| @Hyps.revert.Result u prop ltl P :=
  match hyps with
  | .hyp R n _ =>
    if n = name then .some <| ⟨R, q(tprop(⊤)), (.nul ⟨⟩), q(by simp only [LTL.top_and])⟩ else .none
  | @Hyps.and _ _ _ R S _ h₁ lhs rhs =>
    match (lhs.revert name, rhs.revert name) with
    | (_, .some <| .mk req rest rhs' rel) =>
      .some <| .mk req q(tprop($R ∧ $rest)) (.and ⟨⟩ lhs rhs')
        q(by
          simp [«$rel»]
          apply Eq.symm
          rw [(LTL.bientails_iff_eq tprop((«$R» ∧ «$rest») ∧ «$req») tprop(«$R» ∧ «$rest» ∧ «$req»)).1]
          apply LTL.and_assoc
        )
    | (.some <| .mk req rest lhs' rel, .none) =>
      .some <| .mk req q(tprop($rest ∧ $S)) (.and ⟨⟩ lhs' rhs)
        q(by
          simp only [«$rel»]
          rw [(LTL.bientails_iff_eq tprop((«$rest» ∧ «$S») ∧ «$req») tprop((«$rest» ∧ «$req») ∧ «$S»)).1]
          apply LTLBase.BiEntails.trans _ LTL.and_comm
          apply LTLBase.BiEntails.trans _ LTL.and_assoc
          constructor
          . apply LTL.and_intro
            . apply LTLBase.Entails.trans _ LTL.and_comm.1
              apply LTL.and_elim_l
            . apply LTL.and_elim_r
          . apply LTL.and_intro
            . apply LTLBase.Entails.trans _ LTL.and_comm.1
              apply LTL.and_elim_l
            . apply LTL.and_elim_r
        )
    | (.none, .none) => .none
  | _ => .none




#check LTL.or_elim

#check getMainGoal
#check MVarId.withContext

elab "tcases" name:ident pats:tcasesPat : tactic => do
  -- parse syntax
  -- let pats ← liftMacroM pats -- <| pats.mapM <| iCasesPat.parse

  let mvar ← getMainGoal
  let .some ⟨u, prop, ltl, P, hyps, Q⟩ ← parseLTLGoal (← inferType <| .mvar mvar) | throwError ""
  -- let (mvar, ⟨ u, prop, ltl, hyps, goal ⟩) ← tstart (← getMainGoal)
  mvar.withContext do

    -- process patterns
    let goals ← IO.mkRef #[]
    let pats ← liftMacroM <| tCasesPat.parse pats
    let pf ← introCore pats u prop ltl (fun P goal hyps => do
      let m : Q($P ⊢ $goal) ← mkFreshExprMVarQ <|
        LTLGoal.toExpr { u, prop, ltl, hyps, goal }
      goals.modify (·.push m.mvarId!)
      pure m) P Q hyps

    mvar.assign pf
    replaceMainGoal (← goals.get).toList


