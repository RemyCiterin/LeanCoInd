import Mathlib.Order.FixedPoints
import Qq
import Lean

#check CompleteLattice
#check Lattice
#check OrderHom.lfp

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

-- #check ∀ (x y: L) (h: x ≤ y), h.antisymm
#check LE.le.trans
#check sup_le_sup
#check le_sup_left
#print LinearOrder
#check le_sup_iff
#check infₛ_union

-- instance [inst: ScottContinuousNat f] : ScottContinuousNat (pgfp.union f p) where
--   scottContinuousNat := by
--     intro S
--     rw [infᵢ_le_iff]
--     intro x h₁
--     simp [pgfp.union] at *
--     have h₂ : (p ⊔ infᵢ S) = infᵢ (λ i => p ⊔ S i) := by
--       apply LE.le.antisymm
--       . rw [le_infᵢ_iff]
--         intro i
--         apply sup_le_sup
--         . trivial
--         . rw [infᵢ_le_iff]
--           intro b h₂
--           apply h₂
--       . rw [infᵢ_le_iff]
--         intro y h₂
--
--         have h₃ : (⨅ i:Nat, p) = p := by
--           sorry
--         have h₄ : (⨅ i: Nat, S i) = infᵢ S := by rfl
--         have := infᵢ_sup_infᵢ_le (fun _ => p) S
--         simp only [h₃, h₄] at this
--         --apply LE.le.trans this
--
--
--
--
--     have : p ⊔ infᵢ S ≤ ⨅ i, p ⊔ S i := by sorry
--     have := f.monotone' this
--
--     rw [h₂]
--     have h₃ := @ScottContinuousNat.scottContinuousNat L _ f inst (λ i => p ⊔ S i)
--     apply LE.le.trans _ h₃
--     rw [le_infᵢ_iff]
--     apply h₁




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
section

structure Result {α:Q(Type u)} (E: Q($α) → Type) (e: Q($α)) where
  expr  : Q($α)
  val   : E expr
  proof : Q($e = $expr)

def Result.Id {α:Q(Type u)} {E:Q($α) → Type} (e: Q($α)) (val: E e) : Result E e where
  expr  := e
  val   := val
  proof := q(by rfl)

def Result.map {α:Q(Type u)} {E:Q($α) → Type} {e: Q($α)}
  (r:Result E e) (F:Q($α) → Type) (f: E r.expr → F r.expr) : Result F e where
  expr  := r.expr
  val   := f r.val
  proof := r.proof

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

elab "coind" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply . e)

end

