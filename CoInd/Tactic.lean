import Qq
import Lean
import Std
import CoInd.Attr
import Mathlib.Tactic.SolveByElim

universe u v w

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic Std
open Qq


namespace Tactic.Coinduction

open Lean Expr Elab Term Tactic Meta Qq

#check 42


def Property.parse : List Expr → MetaM ((P: Q(Prop)) × Q($P))
| [x] => do
  let P ← inferType x
  let .sort .zero ← whnf (← inferType P)
    | throwError "{P} most be of type Prop := Sort 0 {x}"
  return ⟨P, x⟩
| x :: xs => do
  let ⟨p, h⟩ ← Property.parse xs
  let P ← inferType x
  let .sort .zero ← whnf (← inferType P)
    | throwError "{P} most be of type Prop := Sort 0 {x}"
  have P : Q(Prop) := P
  have x : Q($P) := x
  return ⟨q($p ∧ $P), q(And.intro $h $x)⟩
| _ => return ⟨q(True), q(True.intro)⟩


def Exists_intro {α: Sort u} (P: α → Prop) (x: α) (h: P x) : Exists P := Exists.intro x h

def matchAppN : Expr → Nat → Option (Expr × List Expr) :=
  λ e n => (λ (x, l) => (x, l.reverse)) <$> go e n
where
  go : Expr → Nat → Option (Expr × List Expr)
  | .mdata _ e, n+1 => go e (n+1)
  | .app e a, n+1 => do
    let (e, l) ← go e n
    return (e, a :: l)
  | e, 0 => some (e, [])
  | _, _ => none

def errorMessage :=
  "A coinduction theorem must be of the form:\n" ++
  "(p: ∀ (x₁:T₁) ... (xₙ:Tₙ) → Prop) → " ++
  "(∀ (x₁:T₁) ... (xₙ:Tₙ), p x₁ ... xₙ → ?coindGoalFn p x₁ ... xₙ) → " ++
  "∀ (x₁:T₁) ... (xₙ:Tₙ), p x₁ ... xₙ → ?goalFn x₁ ... xₙ" ++
  "and the goal must be of the form" ++
  "?goalFn, e₁, ..., eₙ" ++
  "\n"

def parseThmArgs (l: List α) : Option (α × α × List α × α) := do
  let P :: hyp :: args := l | none
  if args.length = 0 then none
  let (args, [h]) := args.splitAt (args.length -1) | none
  return (P, hyp, args, h)

-- the coinduction theorem must be of the form
-- (p: ∀ (x₁:T₁) ... (xₙ:Tₙ) → Prop) →
-- (∀ (x₁:T₁) ... (xₙ:Tₙ), p x₁ ... xₙ → ?coindGoalFn p x₁ ... xₙ) →
-- ∀ (x₁:T₁) ... (xₙ:Tₙ), p x₁ ... xₙ → ?goalFn x₁ ... xₙ
-- and the goal must be of the form
-- ?goalFn, e₁, ..., eₙ
def parseGoal (goal: Expr) (thm: Expr) : MetaM (Expr × List Expr) := do
  forallTelescope thm λ args goalPure => do
    let .some (_, _, args, _) := parseThmArgs args.toList | throwError ("length error: " ++ errorMessage)
    let .some (goalFn, _) := matchAppN goalPure args.length | throwError errorMessage
    let .some (goalFn', exprs) := matchAppN goal args.length | throwError errorMessage
    -- TODO: test if fvars and args are defEq
    if not (←isDefEq goalFn goalFn') then
      throwError "the goal and the coinduction theorem doesn't match"
    return (goalFn, exprs)

elab "coinduction" "[" hyps:term,* "]" "generalizing" "[" args:term,* "]" "using" thm:term : tactic => do
  let thm ← Tactic.elabTerm thm none
  have hyps : Array Term := hyps

  withMainContext do
    let mvarid ← getMainGoal
    let goal ← getMainTarget
    let (goalFn, exprs) ← parseGoal goal (← inferType thm)

    let ⟨P, h⟩ ← Property.parse
      <| List.reverse <| Array.toList <| ← Array.mapM (λ h => Tactic.elabTerm h none) hyps

    let new_goal ← mkFreshExprMVar <| .some <| ← forallTelescope (← inferType thm) λ args goalPure => do
      let .some (_, _, args, _) := parseThmArgs args.toList | throwError errorMessage
      let .some (_, exprs) := matchAppN goal args.length | throwError errorMessage
      let P ← List.foldlM (λ P (e, fv) => do
          mkAppM `And #[← mkAppM `Eq #[e, fv], P]
        ) P (List.zip exprs args)
      mkForallFVars (.mk args) (←mkArrow P goalPure)

    let h ← forallTelescope (← inferType thm) λ args _ => do
      let .some (_, _, args, _) := parseThmArgs args.toList | throwError errorMessage
      let .some (_, exprs) := matchAppN goal args.length | throwError errorMessage
      List.foldlM (λ h e => do
          mkAppM `And.intro #[← mkAppM `Eq.refl #[e], h]
        ) h exprs

    mvarid.assign <| .app (mkAppN new_goal <| .mk exprs) h
    --replaceMainGoal [new_goal.mvarId!, mvarid]

    let (fvars, mvarid) ← new_goal.mvarId!.generalize (← Array.mapM (λ e => do return {expr := ← Tactic.elabTerm e none}) args)

    let (vars, mvarid) ← mvarid.introNP (1 + exprs.length)
    let (vars, [init]) := vars.toList.splitAt (vars.size-1) | unreachable!
    let init := mkFVar init
    replaceMainGoal [mvarid]

    withMainContext $ do
      let P ← inferType init
      let (P_closed, init_closed) ← Array.foldlM (λ (P, h) fv => do
        if containsFVar P fv then do
          let P_fun ← mkLambdaFVars #[mkFVar fv] P
          let P ← mkAppM ``Exists #[←mkLambdaFVars #[mkFVar fv] P]
          let h ← mkAppM ``Tactic.Coinduction.Exists_intro #[P_fun, mkFVar fv, h]
          return ⟨P, h⟩
        else return (P, h)
      ) (P, init) (Array.reverse fvars)
      let sP ← exprToSyntax (← mkLambdaFVars (.mk <| List.map mkFVar vars) P_closed)
      evalTactic <| ← `(tactic|
        apply $(←exprToSyntax thm) $sP ?_ <;> try exact $(← exprToSyntax init_closed);
      )
      evalTactic <| ← `(tactic|
        clear $(←exprToSyntax init);
      )
      let _ ← Array.mapM (λ fv => do evalTactic <| ← `(tactic| clear $(←exprToSyntax (mkFVar fv)))) fvars
      let _ ← List.mapM (λ fv => do evalTactic <| ← `(tactic| try clear $(←exprToSyntax (mkFVar fv)))) vars
      return ()

end Tactic.Coinduction


namespace Mathlib.Tactic.OmegaCompletePartialOrder.Admissible

open Lean Elab Tactic Parser Tactic
open Mathlib Tactic SolveByElim

syntax (name := refinment_type) "refinment_type" : tactic

elab_rules : tactic
| `(tactic| refinment_type ) => do
  let cfg ← elabApplyRulesConfig <| mkNullNode #[]
  let cfg := { cfg.noBackTracking with
    transparency := .reducible
    failAtMaxDepth := false
    exfalso := false }
  liftMetaTactic fun g => do solveByElim.processSyntax cfg false false [] [] #[mkIdent `refinment_type] [g]


end Mathlib.Tactic.OmegaCompletePartialOrder.Admissible


