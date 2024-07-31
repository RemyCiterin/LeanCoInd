import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteBooleanAlgebra
import Qq
import Lean

#check CompleteLattice
#check Lattice
#check OrderHom.lfp

#check inferInstanceAs <| CompleteDistribLattice (∀ x:Nat, Nat → Prop)
#check inferInstanceAs <| CompleteBooleanAlgebra (∀ x:Nat, {y: Nat // y == x} → Prop)

universe u v w

section


variable {α:Type u} (f: (α → Prop) →o (α → Prop))

#print Set
#print CompleteLattice
#print SupSet.supₛ
#print Lattice
#print Preorder

-- A type class for `indexed scott continuity` with natural numbers as index
class ScottContinuousNat (foo: (α → Prop) →o (α → Prop)) where
  scottContinuousNat : ∀ (S: Nat → α → Prop) (x: α),
    (∀ i, foo (S i) x) → foo (λ y => ∀ i, S i y) x


-- generate an approximation of size `n` of the greatest fixed point of `f`
def gfp₁.approx : Nat → (α → Prop) →o (α → Prop)
| 0 => {toFun := λ _ => ⊤, monotone' := by intro a b _; rfl}
| n + 1 => {
    toFun := λ x => f (approx n x),
    monotone' := by
      intro a b h₁
      apply f.monotone'
      apply (approx n).monotone'
      assumption
  }

def gfp₁.scott : α → Prop := λ x => ∀ i, approx f i ⊤  x

def gfp₁.scott.tarski [ScottContinuousNat f] :
  ∀ p, (p ≤ f p) → p ≤ scott f := by
  intro p h₁
  simp only [scott, le_infᵢ_iff]
  intro x h n
  induction n generalizing h x with
  | zero =>
    simp only [approx]
    trivial
  | succ n h₂ =>
    simp only [approx]
    have h₃ := f.monotone' h₂ _ (h₁ x h)
    exact h₃

def gfp₁.scott.scott_f_leq_f_scott_f [inst: ScottContinuousNat f] :
  scott f ≤ f (scott f) := by
  have h₁ := inst.scottContinuousNat
  simp only [scott]
  simp [infᵢ_le_iff]
  conv at h₁ =>
    intro S
    rfl
  intro a h₂
  have h₃ := λ i => h₂ (.succ i)
  simp only [approx] at h₃
  specialize h₁ (λ i => approx f i ⊤) a h₃
  assumption

def gfp₁ := @OrderHom.gfp (α → Prop) _

def gfp₁.tarski :
  ∀ p, (p ≤ f p) → p ≤ gfp₁ f := by
  intro p h₁
  apply OrderHom.le_gfp
  assumption

@[simp] def gfp₁.unfold :
  f (gfp₁ f) = gfp₁ f := by
  simp only [gfp₁, OrderHom.map_gfp]

def gfp₁.strong_coind :
  ∀ p, (p ≤ f (p ⊔ gfp₁ f)) → p ≤ gfp₁ f := by
  intro p
  have h₁ := tarski f (p ⊔ gfp₁ f)
  intro h₂ x h₃
  apply h₁
  . rintro x (h|h)
    . apply h₂
      assumption
    . apply @OrderHom.monotone' _ _ _ _ f (gfp₁ f)
      . intro _ h
        apply Or.inr
        assumption
      . rw [unfold]
        assumption
  apply Or.inl
  assumption



def gfp₁.scott.scott_leq_gfp [inst: ScottContinuousNat f] :
  scott f ≤ gfp₁ f := by
  apply gfp₁.tarski
  apply gfp₁.scott.scott_f_leq_f_scott_f

def gfp₁.scott.gfp_leq_scott [inst: ScottContinuousNat f] :
  gfp₁ f ≤ scott f := by
  apply scott.tarski
  simp only [gfp₁, OrderHom.map_gfp, le_refl]

-- the `rewriting theorem` allow to apply coinduction by induction over the depth of the coinductive prediacte
def gfp₁.scott.rewrite [inst: ScottContinuousNat f] :
  gfp₁ f = scott f := by
  apply (gfp_leq_scott f).antisymm
  exact scott_leq_gfp f

@[simp] def gfp₁.scott.unfold [inst: ScottContinuousNat f] :
  f (scott f) = scott f := by
  rw [←scott.rewrite f]
  simp [gfp₁, OrderHom.map_gfp]

def gfp₁.scott.strong_coind [inst:ScottContinuousNat f] :
  ∀ p, (p ≤ f (p ⊔ gfp₁.scott f)) → p ≤ gfp₁.scott f := by
  have h := gfp₁.strong_coind f
  rw [gfp₁.scott.rewrite] at h
  assumption

def pgfp₁.union  (p: α → Prop) : (α → Prop) →o (α → Prop) where
  toFun q := f (p ⊔ q)
  monotone' :=
    by
      intro a b leq
      apply f.monotone'
      apply sup_le
      . simp
      . apply le_sup_of_le_right
        assumption

-- if L is a `CompleteDistribLattice`, then `pgfp.union f p` is Scott continuous if `f` is Scott continuous
instance {p: α → Prop} [inst: ScottContinuousNat f] :
  ScottContinuousNat (pgfp₁.union f p) where
  scottContinuousNat := by
    intro S

    have h₂ : (λ x => ∀ i, p x ∨ S i x) ≤ p ⊔ (λ x => ∀ i, S i x) := by
      intro x h₁
      by_cases p x
      . apply Or.inl
        assumption
      . apply Or.inr
        intro n
        specialize h₁ n
        simp [h] at h₁
        assumption

    intro x h₁
    simp [pgfp₁.union] at *

    have h₃ := f.monotone' h₂
    apply h₃
    have h₄ := inst.scottContinuousNat (λ i => p ⊔ S i)
    apply h₄
    exact h₁

def pgfp₁ : (α → Prop) →o (α → Prop) where
  toFun p :=
    gfp₁ (pgfp₁.union f p)

  monotone' :=
    by
      intro a b leq
      apply OrderHom.gfp.monotone'
      intro q
      apply f.monotone'
      apply sup_le
      . apply le_sup_of_le_left
        assumption
      . simp

def pgfp₁.approx (p: α → Prop) (n: Nat) : (α → Prop) →o (α → Prop) :=
  gfp₁.approx (pgfp₁.union f p) n

def pgfp₁.scott (p: α → Prop) : α → Prop := gfp₁.scott (pgfp₁.union f p)

def pgfp₁.unfold (p:α → Prop) :
  f (p ⊔ pgfp₁ f p) = pgfp₁ f p :=
by
  have : union f p (pgfp₁ f p) = pgfp₁ f p := by simp [pgfp₁]
  simp only [union] at this
  assumption

#check le_trans

open OrderHom in
def pgfp₁.accumulate (p q:α → Prop) :
  q ≤ pgfp₁ f p ↔ q ≤ pgfp₁ f (p ⊔ q) :=
by
  simp only [pgfp₁, ge_iff_le]
  constructor <;> intro h
  . have : union f p ≤ union f (p ⊔ q) := by
      simp only [union, ge_iff_le, mk_le_mk]
      intro x
      apply f.monotone'
      apply sup_le
      . apply le_sup_of_le_left
        simp
      . apply le_sup_of_le_right
        simp
    have := gfp.monotone' this
    apply le_trans _ this
    assumption

  . have := @le_trans _ _ q (gfp₁ (union f (p ⊔ q))) (gfp₁ (union f p))
    apply this h

    have : gfp (union f (p ⊔ q)) ≤ f (p ⊔ gfp (union f (p ⊔ q))) := by
      conv =>
        lhs
        rw [<-isFixedPt_gfp]
        lhs
        simp only [union]
        rfl
      simp only
      apply f.monotone'
      apply sup_le
      . apply sup_le
        . simp
        . intro x h₁
          specialize h x h₁
          apply Or.inr h
      . simp
    apply le_gfp
    apply this

def pgfp₁.coinduction (p:α → Prop) :
  p ≤ pgfp₁ f ⊥ ↔ p ≤ f (p ⊔ pgfp₁ f p) :=
by
  simp only [pgfp₁.unfold]
  rw [pgfp₁.accumulate]
  simp [Sup.sup, Bot.bot]

def pgfp.monotone (p q:α → Prop) :
  p ≤ q → pgfp₁ f p ≤ pgfp₁ f q := by
  apply (pgfp₁ f).2


def pgfp₁.scott.rewrite (f: (α → Prop) →o α → Prop) [ScottContinuousNat f]
  : pgfp₁ f = pgfp₁.scott f := by
  conv =>
    rhs
    simp [scott]
    intro p
    simp only [←gfp₁.scott.rewrite (pgfp₁.union f p)]
    rfl

end

section
variable {α β: Type u}

theorem pgfp₁.theorem (f: (α → Prop) →o (α → Prop)) (p: α → Prop) :
  (∀ x, p x → f (p ⊔ pgfp₁ f p) x) → ∀ x, p x → pgfp₁ f ⊥ x :=
  λ h₁ x h₂ => (coinduction f p).2 h₁ x h₂
end

/-
A coinduction is the application of a lemma `pgfp.theorem` but we have to find x and p using the current
goal an hypothesis

A coinduction theorem is a theorem of the form

  (∀A, P A → ...) → ∀A, P A → ?goal A
  and we want to apply it on goals of the form
  ∀ B, ?goal Exprs

  so we have to modify

-/


open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic
open Qq


namespace Tactic.pgfp₁

open Lean Expr Elab Term Tactic Meta Qq

/-- tactic for proof by bisimulation on streams -/
syntax "pgfp₁" (ppSpace colGt term) (" with" (ppSpace colGt binderIdent)+)? : tactic
syntax "pgfp₂" (ppSpace colGt term) (" with" (ppSpace colGt binderIdent)+)? : tactic


def matchPGFP? (e:Q(Prop)) : MetaM (Option (Expr × Expr)) :=
  match e with
  | .app _ x => do
    let t ← inferType x
    return .some (t, x)
  | .mdata _ e => matchPGFP? e
  | _ => return .none


#check matchEq?

elab_rules : tactic
  | `(tactic| pgfp₁ $e $[ with $ids:binderIdent*]?) => do
    let ids : TSyntaxArray `Lean.binderIdent := ids.getD #[]
    let idsn (n : ℕ) : Name :=
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => n.getId
        | `(binderIdent| _) => `_
        | _ => unreachable!
      | none => `_
    let idss (n : ℕ) : TacticM (TSyntax `rcasesPat) := do
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => `(rcasesPat| $n)
        | `(binderIdent| _%$b) => `(rcasesPat| _%$b)
        | _ => unreachable!
      | none => `(rcasesPat| _)
    withMainContext do
      let e ← Tactic.elabTerm e none
      let f ← liftMetaTacticAux fun g => do
        let (#[fv], g) ← g.generalize #[{ expr := e }] | unreachable!
        return (mkFVar fv, [g])
      withMainContext do
        let some (t, l) ← matchPGFP? (←getMainTarget) | throwError "goal is not an application"
        let ex ←
          withLocalDecl (idsn 1) .default t fun v₀ => do
            let x₀ ← mkEq v₀ l
            let ex₁ ← mkLambdaFVars #[f] x₀
            let ex₂ ← mkAppM ``Exists #[ex₁]
            mkLambdaFVars #[v₀] ex₂
        let R ← liftMetaTacticAux fun g => do
          let g₁ ← g.define (idsn 0) (← mkArrow t (mkSort .zero)) ex
          let (Rv, g₂) ← g₁.intro1P
          return (mkFVar Rv, [g₂])
        withMainContext do
          ids[0]?.forM fun s => addLocalVarInfoForBinderIdent R s
          let sR ← exprToSyntax R
          evalTactic <| ← `(tactic|
            refine pgfp₁.theorem _ $sR ?_ _ ⟨_, rfl⟩;
            rintro $(← idss 1) $(← idss 2))
          liftMetaTactic fun g => return [← g.clear f.fvarId!]
    for n in [6 : ids.size] do
      let name := ids[n]!
      logWarningAt name m!"unused name: {name}"

#check MVarId.generalize



#check 42

-- represent a goal of the form `@pgfp₁.{u} α f p x`
structure Goal where
  u: Level
  α: Q(Type u)
  f: Q(($α → Prop) →o $α → Prop)
  p: Q($α → Prop)
  x: Q($α)

def Goal.toExpr : Goal → Q(Prop)
| ⟨u, α, f, p, x⟩ => q(@pgfp₁.{u} $α $f $p $x)

#check pgfp₁
def Goal.parse (expr: Expr) : MetaM Goal := do
  let .sort .zero ← whnf (← inferType expr)
    | throwError s!"the goal must be a property, found {← whnf (← inferType expr)}"
  have expr : Q(Prop) := expr
  match expr with
  | ~q(@pgfp₁ $α $F $p $x) =>
    let .sort (.succ u) ← whnf (← inferType α)
      | throwError s!"{α} must be of type `Type u`"
    return ⟨u, α, F, p, x⟩
  | _ =>
    throwError "the goal is not a parametrized fixed-point"

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

#check liftMetaTacticAux

def Exists_intro {α: Sort u} (P: α → Prop) (x: α) (h: P x) : Exists P := Exists.intro x h

elab "custom_pgfp" "[" h:term,* "]" "generalizing" "[" args:term,* "]"  : tactic => do

  withMainContext do
    let mvarid ← getMainGoal
    let goal ← getMainTarget
    let ⟨u, α, f, p, e⟩ ← Goal.parse goal
    let ⟨P, h⟩ ← Property.parse <| List.reverse <| Array.toList <| ← Array.mapM (λ h => Tactic.elabTerm h none) h

    let new_goal : Q(∀ x, x = $e ∧ $P → pgfp₁ $f $p x) ← mkFreshExprMVarQ q(∀ x, x = $e ∧ $P → pgfp₁ $f $p x)
    mvarid.assign q($new_goal $e ⟨rfl, $h⟩)

    let (fvars, mvarid) ← new_goal.mvarId!.generalize (← Array.mapM (λ e => do return {expr := ← Tactic.elabTerm e none}) args)

    let (#[e, init], mvarid) ← mvarid.introNP 2 | unreachable!
    let init := mkFVar init
    replaceMainGoal [mvarid]

    withMainContext $ do
      let g ← getMainTarget
      dbg_trace f!"{← instantiateMVars g}"
      let sF ← exprToSyntax f
      let P ← inferType init
      let (P_closed, init_closed) ← Array.foldlM (λ (P, h) fv => do
        if containsFVar P fv then do
          let P_fun ← mkLambdaFVars #[mkFVar fv] P
          let P ← mkAppM ``Exists #[←mkLambdaFVars #[mkFVar fv] P]
          let h ← mkAppM ``Tactic.pgfp₁.Exists_intro #[P_fun, mkFVar fv, h]
          return ⟨P, h⟩
        else return (P, h)
      ) (P, init) (Array.reverse fvars)
      let sP ← exprToSyntax (← mkLambdaFVars #[mkFVar e] P_closed)
      evalTactic <| ← `(tactic|
        apply pgfp₁.theorem $sF $sP ?_ _ $(← exprToSyntax init_closed);
        clear $(←exprToSyntax init);
      )
      let _ ← Array.mapM (λ fv => do evalTactic <| ← `(tactic| clear $(←exprToSyntax (mkFVar fv)))) fvars
      return ()

#check containsFVar
#check Array.foldlM
#check pgfp₁.theorem
#check abstract
#check mkLambdaFVars
#check Lean.MVarId.generalizeHyp
#check Lean.MVarId.generalize
#print GeneralizeArg
#check mkFVar
#check intro1P
#print FVarSubst
#check Nat.le_refl
#check MVarId.introNP


def forallℕ (P: Nat → Prop) : (Nat → Prop) →o Nat → Prop where
  toFun r n := P n ∧ r (n+1)
  monotone' := by
    intro r s h₁ n ⟨h₂, h₃⟩
    constructor
    . assumption
    . apply h₁
      assumption

example : pgfp₁ (forallℕ λ n => n > 0) ⊥ 1 := by
  let one : Nat := 1
  have h₁ : 1 = one := Eq.refl 1
  rw [h₁]
  have h₂ : 1 ≤ one ∧ True := by simp_arith
  custom_pgfp [h₂, True.intro] generalizing [one, 2]
  rintro n ⟨m, eq, ⟨h₁, _⟩, _⟩
  induction eq
  constructor
  . simp_arith [*]
  . apply Or.inl
    simp_arith [*]

end Tactic.pgfp₁

