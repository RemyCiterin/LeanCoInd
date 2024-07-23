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

variable {L:Type u} [CompleteLattice L] (f: L →o L)

#print Set
#print CompleteLattice
#print SupSet.supₛ
#print Lattice
#print Preorder

-- A type class for `indexed scott continuity` with natural numbers as index
class ScottContinuousNat (foo: L →o L) where
  scottContinuousNat : ∀ (S: Nat → L),
    (⨅ i, foo (S i)) ≤ foo (infᵢ S)


-- generate an approximation of size `n` of the greatest fixed point of `f`
def gfp.approx : Nat → L →o L
| 0 => {toFun := λ _ => ⊤, monotone' := by intro a b _; rfl}
| n + 1 => {
    toFun := λ x => f (approx n x),
    monotone' := by
      intro a b h₁
      apply f.monotone'
      apply (approx n).monotone'
      assumption
  }

def gfp.scott : L := ⨅ i, approx f i ⊤

def gfp.scott.tarski [ScottContinuousNat f] :
  ∀ p, p ≤ f p → p ≤ scott f := by
  intro p h₁
  simp only [scott, le_infᵢ_iff]
  intro i
  induction i with
  | zero =>
    simp only [approx, le_top]
  | succ n h₂ =>
    apply le_trans h₁
    apply f.monotone'
    assumption

def gfp.scott.scott_f_leq_f_scott_f [inst: ScottContinuousNat f] :
  scott f ≤ f (scott f) := by
  have h₁ := @ScottContinuousNat.scottContinuousNat L _ f inst
  simp only [scott]
  simp [infᵢ_le_iff]
  conv at h₁ =>
    intro S
    rw [infᵢ_le_iff]
    rfl
  intro a h₂
  have h₃ := λ i => h₂ (.succ i)
  simp only [approx] at h₃
  specialize h₁ (λ i => approx f i ⊤) a h₃
  assumption

def gfp.scott.scott_leq_gfp [inst: ScottContinuousNat f] :
  scott f ≤ OrderHom.gfp f := by
  apply OrderHom.le_gfp
  apply gfp.scott.scott_f_leq_f_scott_f

def gfp.scott.gfp_leq_scott [inst: ScottContinuousNat f] :
  OrderHom.gfp f ≤ scott f := by
  apply scott.tarski
  simp only [OrderHom.map_gfp, le_refl]

def gfp.scott.gfp_eq_scott [inst: ScottContinuousNat f] :
  OrderHom.gfp f = scott f := by
  apply (gfp_leq_scott f).antisymm
  exact scott_leq_gfp f

@[simp] def gfp.scott.unfold [inst: ScottContinuousNat f] :
  f (scott f) = scott f := by
  rw [←gfp_eq_scott f]
  simp [OrderHom.map_gfp]


def pgfp.union  (p: L) : L →o L where
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
instance {L:Type u} [CompleteDistribLattice L] {f: L →o L} {p: L} [inst: ScottContinuousNat f] : ScottContinuousNat (pgfp.union f p) where
  scottContinuousNat := by
    intro S


    have h₂ : (⨅ i, p ⊔ S i) ≤ p ⊔ infᵢ S := by
      have := sup_infᵢ_eq p S
      rw [←this]
      simp only [ge_iff_le, le_infᵢ_iff, le_refl]

    rw [infᵢ_le_iff]
    intro x h₁
    simp [pgfp.union] at *

    have h₃ := f.monotone' h₂
    apply LE.le.trans _ h₃
    have h₄ := @ScottContinuousNat.scottContinuousNat L _ f inst (λ i => p ⊔ S i)
    apply LE.le.trans _  h₄
    rw [le_infᵢ_iff]
    exact h₁

def pgfp : L →o L where
  toFun p :=
    OrderHom.gfp (pgfp.union f p)

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

def pgfp.approx (p: L) (n: Nat) : L →o L := gfp.approx (pgfp.union f p) n

def pgfp.scott (p: L) : L := gfp.scott (pgfp.union f p)

-- def pgfp.scott.thm (p: L) [ScottContinuousNat f] : pgfp f = pgfp.scott f := by
--   simp [gfp.scott.gfp_eq_scott (pgfp.union f p)]
--   sorry

def pgfp.unfold (p:L) :
  f (p ⊔ pgfp f p) = pgfp f p :=
by
  have : union f p (pgfp f p) = pgfp f p := by simp [pgfp]
  simp only [union] at this
  assumption

open OrderHom in
def pgfp.accumulate (p q:L) :
  q ≤ pgfp f p ↔ q ≤ pgfp f (p ⊔ q) :=
by
  simp only [pgfp, ge_iff_le]
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

  . apply le_trans h
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
        . apply le_trans h
          simp
      . simp
    apply le_gfp
    assumption

def CompleteLattice.bot_sup (p:L) :
  ⊥ ⊔ p = p := by
  simp

def CompleteLattice.sup_bot (p:L) :
  p ⊔ ⊥ = p := by
  simp

def pgfp.coinduction (p:L) :
  p ≤ pgfp f ⊥ ↔ p ≤ f (p ⊔ pgfp f p) :=
by
  simp only [pgfp.unfold]
  rw [pgfp.accumulate]
  rw [CompleteLattice.bot_sup]

def pgfp.monotone (p q:L) :
  p ≤ q → pgfp f p ≤ pgfp f q := by
  apply (pgfp f).2

end

section
variable {α: Type u}

theorem pgfp.theorem (f: (α → Prop) →o (α → Prop)) (p: α → Prop) :
  (∀ x, p x → f (p ⊔ pgfp f p) x) → ∀ x, p x → pgfp f ⊥ x :=
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


def matchPGFP? (e:Q(Prop)) : MetaM (Option (Expr × Expr)) :=
  match e with
  | .app _ x => do
    let t ← inferType x
    return .some (t, x)
  | _ => return .none

def matchPGFP2? (e:Q(Prop)) : MetaM (Option (Expr × Expr × Expr × Expr)) :=
  match e with
  | .app (.app _ x) y => do
    let tx ← inferType x
    let ty ← inferType y
    return .some ⟨tx, x, ty, y⟩
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
            refine pgfp.theorem _ $sR ?_ _ ⟨_, rfl⟩;
            rintro $(← idss 1) $(← idss 2))
          liftMetaTactic fun g => return [← g.clear f.fvarId!]
    for n in [6 : ids.size] do
      let name := ids[n]!
      logWarningAt name m!"unused name: {name}"

end Tactic.pgfp₁

