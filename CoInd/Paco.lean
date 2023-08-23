import Mathlib
import Mathlib.Order.FixedPoints

#check CompleteLattice
#check Lattice
#check OrderHom.lfp

universe u v w


section

variable {L:Type u} [CompleteLattice L] (f: L →o L)

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

end

