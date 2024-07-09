import Lean.PrettyPrinter.Delaborator
import CoInd.Std.DelabRule
import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils


import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq


open Lean Lean.Macro

-- definition of a syntax for temporal proerties
syntax:max "tprop(" term ")" : term
syntax:max "term(" term ")" : term

macro_rules
| `(tprop(term($t))) => pure t
| `(tprop($t)) => pure t

macro_rules
| `(tprop(($P))) => ``((tprop($P)))
| `(tprop($P $[ $Q]*)) => ``($P $[ $Q]*)
| `(tprop(if $c then $t else $e)) => ``(if $c then tprop($t) else tprop($e))

partial def unpackTprop [Monad M] [MonadRef M] [MonadQuotation M] : Term → M Term
| `(tprop($P)) => do `($P)
| `($P:ident) => do `($P)
| `(?$P:ident) => do `(?$P)
| `(($P)) => do `(($(← unpackTprop P)))
| `($P $[ $Q]*) => do ``($P $[ $Q]*)
| `(if $c then $t else $e) => do `(if $c then $(← unpackTprop t) else $(← unpackTprop e))
| `(($P : $t)) => do ``(($(← unpackTprop P) : $t))
| `($t) => `($t:term)


class LTLBase (PROP: Type u) where
  Entails : PROP → PROP → Prop

  And : PROP → PROP → PROP
  Imp : PROP → PROP → PROP
  Pure : Prop → PROP
  Or : PROP → PROP → PROP
  Until : PROP → PROP → PROP
  Next : PROP → PROP

def LTLBase.Not {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP := Imp p (Pure False)
def LTLBase.Iff {PROP: Type u} [LTLBase PROP] (p₁ p₂: PROP) : PROP := And (Imp p₁ p₂) (Imp p₂ p₁)
def LTLBase.Diamond {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP := Until (Pure True) p
def LTLBase.Square {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP := Not (Diamond (Not p))

macro:25 P:term:29 " ⊢ " Q:term:25 : term => ``(LTLBase.Entails tprop($P) tprop($Q)) -- type as \entails or \vdash
macro:25 " ⊢ " Q:term:25 : term => ``(LTLBase.Entails (LTLBase.Pure True) tprop($Q))

delab_rule LTLBase.Entails
| `($_ $P $Q) => do ``($(← unpackTprop P) ⊢ $(← unpackTprop Q))

syntax:35 term:36 "∪" term:35: term -- type as \union
syntax:max "∘ " term:40 : term -- type as \circ
syntax:max "□ " term:40 : term -- type as \square
syntax:max "⋄ " term:40 : term -- type as \diamond
syntax "⌜" term "⌝" : term -- type as ulc and \urc
syntax "⊤" : term -- type as \top
syntax "⊥" : term -- type as \bot

macro_rules
| `(tprop($P ∧ $Q)) => ``(LTLBase.And tprop($P) tprop($Q))
| `(tprop($P ∨ $Q)) => ``(LTLBase.Or tprop($P) tprop($Q))
| `(tprop($P → $Q)) => ``(LTLBase.Imp tprop($P) tprop($Q))
| `(tprop($P ↔ $Q)) => ``(LTLBase.Iff tprop($P) tprop($Q))
| `(tprop($P ∪ $Q)) => ``(LTLBase.Until tprop($P) tprop($Q))
| `(tprop(⌜ $P ⌝)) => ``(LTLBase.Pure $P)
| `(tprop(¬$P)) => ``(LTLBase.Not tprop($P))
| `(tprop(□$P)) => ``(LTLBase.Square tprop($P))
| `(tprop(∘$P)) => ``(LTLBase.Next tprop($P))
| `(tprop(⋄$P)) => ``(LTLBase.Diamond tprop($P))
| `(tprop(⊤)) => ``(LTLBase.Pure True)
| `(tprop(⊥)) => ``(LTLBase.Pure False)

delab_rule LTLBase.And
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ∧ $(← unpackTprop Q)))
delab_rule LTLBase.Or
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ∨ $(← unpackTprop Q)))
delab_rule LTLBase.Imp
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) → $(← unpackTprop Q)))
delab_rule LTLBase.Iff
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ↔ $(← unpackTprop Q)))
delab_rule LTLBase.Until
| `($_ $P $Q) => do ``(tprop($(← unpackTprop P) ∪ $(← unpackTprop Q)))
delab_rule LTLBase.Not
| `($_ $P) => do ``(tprop(¬$(← unpackTprop P)))
delab_rule LTLBase.Next
| `($_ $P) => do ``(tprop(∘$(← unpackTprop P)))
delab_rule LTLBase.Square
| `($_ $P) => do ``(tprop(□$(← unpackTprop P)))
delab_rule LTLBase.Diamond
| `($_ $P) => do ``(tprop(⋄$(← unpackTprop P)))
delab_rule LTLBase.Pure
| `($_ $P) => do ``(tprop(⌜$P⌝))

delab_rule LTLBase.Pure
| `($_ False) => do ``(tprop(⊥))
| `($_ True) => do ``(tprop(⊤))



structure LTLBase.BiEntails {PROP: Type u} [LTLBase PROP] (P Q: PROP) : Prop where
  mp : P ⊢ Q
  mpr: Q ⊢ P

macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(LTLBase.BiEntails tprop($P) tprop($Q)) -- type as \dashv\entails

delab_rule LTLBase.BiEntails
  | `($_ $P $Q) => do ``($(← unpackTprop P) ⊣⊢ $(← unpackTprop Q))

delab_rule LTLBase.Entails
| `($_ tprop(⌜ True ⌝) $P) => do ``(⊢ $(← unpackTprop P))

#check ∀ (PROP: Type) [LTLBase PROP] (A B C D: PROP), tprop((A → ⋄B) → (C → D)) ⊢ tprop(C ∧ D)

class LTL (PROP: Type u) extends LTLBase PROP where
  entails_transitive : Transitive Entails
  entails_reflexive : Reflexive Entails

  bientails_iff_eq (P Q: PROP) : LTLBase.BiEntails P Q ↔ P = Q

  and_elim_l {P Q: PROP} : P ∧ Q ⊢ P
  and_elim_r {P Q: PROP} : P ∧ Q ⊢ Q
  and_intro {P Q R: PROP} : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R

  or_intro_l {P Q: PROP} : P ⊢ P ∨ Q
  or_intro_r {P Q: PROP} : Q ⊢ P ∨ Q
  or_elim {P Q R: PROP} : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R

  imp_intro {P Q R: PROP} : (P ∧ Q ⊢ R) → P ⊢ (Q → R)
  imp_elim {P Q R: PROP} : (P ⊢ Q → R) → (P ∧ Q ⊢ R)

  pure_intro {ψ: Prop} {P: PROP} : ψ → (P ⊢ ⌜ φ ⌝)
  pure_elim' {ψ: Prop} {P: PROP} : (ψ → ⊢ P) → ⌜ψ⌝ ⊢ P


namespace StreamProp

def TProp := Nat → Prop

instance : LTLBase TProp where
  Entails p₁ p₂ := ∀ n, p₁ n → p₂ n
  Imp p₁ p₂ n := p₁ n → p₂ n
  And p₁ p₂ n := p₁ n ∧ p₂ n
  Or p₁ p₂ n := p₁ n ∨ p₂ n
  Pure p _ := p
  Until p₁ p₂ n := ∃ k, n ≤ k ∧ (∀ i, n ≤ i → i < k → p₁ i) ∧ p₂ k
  Next p n := p (n+1)

instance : LTL TProp where
  entails_transitive :=
    fun p₁ p₂ p₃ h₁ h₂ n h₃ => h₂ n (h₁ n h₃)

  entails_reflexive := fun x n h₁ => h₁

end StreamProp

def LTLBase.Entails.trans {P Q R: PROP} [LTL PROP] (h₁: P ⊢ Q) (h₂: Q ⊢ R) : P ⊢ R := LTL.entails_transitive h₁ h₂
def LTLBase.BiEntails.trans {P Q R: PROP} [LTL PROP] (h₁: P ⊣⊢ Q) (h₂: Q ⊣⊢ R) : P ⊣⊢ R := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
def LTLBase.Entails.rfl {P: PROP} [LTL PROP] : P ⊢ P := LTL.entails_reflexive P
def LTLBase.BiEntails.rfl {P: PROP} [LTL PROP] : P ⊣⊢ P := ⟨.rfl, .rfl⟩

namespace LTL
variable {PROP: Type u} [inst: LTL PROP]


instance entails_trans : Trans (α := PROP) inst.Entails inst.Entails inst.Entails where
  trans h₁ h₂ := h₁.trans h₂

theorem and_elim_l' {P Q R: PROP} (h: P ⊢ R) : P ∧ Q ⊢ R := entails_trans.trans and_elim_l h
theorem and_elim_r' {P Q R: PROP} (h: Q ⊢ R) : P ∧ Q ⊢ R := entails_trans.trans and_elim_r h

theorem or_intro_l' {P Q R: PROP} (h: P ⊢ Q) : P ⊢ Q ∨ R := h.trans or_intro_l
theorem or_intro_r' {P Q R: PROP} (h: P ⊢ R) : P ⊢ Q ∨ R := h.trans or_intro_r


theorem and_symm {P Q:PROP} : P ∧ Q ⊢ Q ∧ P := and_intro and_elim_r and_elim_l
theorem mp {P Q R: PROP} (h₁: P ⊢ Q → R) (h₂: P ⊢ Q) : P ⊢ R :=
  entails_trans.trans (and_intro .rfl h₂) (imp_elim h₁)

theorem imp_intro' {P Q R: PROP} (h: Q ∧ P ⊢ R) : P ⊢ Q → R := imp_intro <| and_symm.trans h

theorem imp_elim' {P Q R : PROP} (h : Q ⊢ P → R) : P ∧ Q ⊢ R :=
  and_symm.trans <| imp_elim h

theorem imp_elim_l {P Q : PROP} : (P → Q) ∧ P ⊢ Q := imp_elim .rfl

theorem imp_elim_r {P Q : PROP} : P ∧ (P → Q) ⊢ Q := imp_elim' .rfl

theorem false_elim {P : PROP} : ⊥ ⊢ P := pure_elim' False.elim

theorem true_intro {P : PROP} : P ⊢ ⊤ := pure_intro trivial

-- @[rw_mono_rule]
theorem and_mono {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∧ P' ⊢ Q ∧ Q' :=
  and_intro (and_elim_l' h1) (and_elim_r' h2)

theorem and_mono_l {P P' Q : PROP} (h : P ⊢ P') : P ∧ Q ⊢ P' ∧ Q := and_mono h .rfl

theorem and_mono_r {P Q Q' : PROP} (h : Q ⊢ Q') : P ∧ Q ⊢ P ∧ Q' := and_mono .rfl h

--@[rw_mono_rule]
theorem and_congr {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∧ P' ⊣⊢ Q ∧ Q' :=
  ⟨and_mono h1.1 h2.1, and_mono h1.2 h2.2⟩

theorem and_congr_l {P P' Q : PROP} (h : P ⊣⊢ P') : P ∧ Q ⊣⊢ P' ∧ Q := and_congr h .rfl

theorem and_congr_r {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∧ Q ⊣⊢ P ∧ Q' := and_congr .rfl h

--@[rw_mono_rule]
theorem or_mono {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∨ P' ⊢ Q ∨ Q' :=
  or_elim (or_intro_l' h1) (or_intro_r' h2)

theorem or_mono_l {P P' Q : PROP} (h : P ⊢ P') : P ∨ Q ⊢ P' ∨ Q := or_mono h .rfl

theorem or_mono_r {P Q Q' : PROP} (h : Q ⊢ Q') : P ∨ Q ⊢ P ∨ Q' := or_mono .rfl h

--@[rw_mono_rule]
theorem or_congr {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∨ P' ⊣⊢ Q ∨ Q' :=
  ⟨or_mono h1.1 h2.1, or_mono h1.2 h2.2⟩

theorem or_congr_l {P P' Q : PROP} (h : P ⊣⊢ P') : P ∨ Q ⊣⊢ P' ∨ Q := or_congr h .rfl

theorem or_congr_r {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∨ Q ⊣⊢ P ∨ Q' := or_congr .rfl h

--@[rw_mono_rule]
theorem imp_mono {P P' Q Q' : PROP} (h1 : Q ⊢ P) (h2 : P' ⊢ Q') : (P → P') ⊢ Q → Q' :=
  imp_intro <| (and_mono_r h1).trans <| (imp_elim .rfl).trans h2

theorem imp_mono_l {P P' Q : PROP} (h : P' ⊢ P) : (P → Q) ⊢ (P' → Q) := imp_mono h .rfl

theorem imp_mono_r {P Q Q' : PROP} (h : Q ⊢ Q') : (P → Q) ⊢ (P → Q') := imp_mono .rfl h

--@[rw_mono_rule]
theorem imp_congr {P P' Q Q' : PROP}
    (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : (P → P') ⊣⊢ (Q → Q') :=
  ⟨imp_mono h1.2 h2.1, imp_mono h1.1 h2.2⟩

theorem imp_congr_l {P P' Q : PROP} (h : P ⊣⊢ P') : (P → Q) ⊣⊢ (P' → Q) :=
  imp_congr h .rfl

theorem imp_congr_r {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P → Q) ⊣⊢ (P → Q') :=
  imp_congr .rfl h

theorem and_self {P : PROP} : P ∧ P ⊣⊢ P := ⟨and_elim_l, and_intro .rfl .rfl⟩
--instance : Idempotent (α := PROP) BiEntails and := ⟨and_self⟩

theorem or_self {P : PROP} : P ∨ P ⊣⊢ P := ⟨or_elim .rfl .rfl, or_intro_l⟩
--instance : Idempotent (α := PROP) BiEntails or := ⟨or_self⟩

theorem and_comm {P : PROP} : P ∧ Q ⊣⊢ Q ∧ P := ⟨and_symm, and_symm⟩
--instance : Commutative (α := PROP) BiEntails and := ⟨and_comm⟩

theorem true_and {P : PROP} : ⊤ ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
--instance : LeftId (α := PROP) BiEntails tprop(True) and := ⟨true_and⟩

theorem and_true {P : PROP} : P ∧ ⊤ ⊣⊢ P := and_comm.trans true_and
--instance : RightId (α := PROP) BiEntails tprop(True) and := ⟨and_true⟩

theorem and_assoc {P Q R : PROP} : (P ∧ Q) ∧ R ⊣⊢ P ∧ Q ∧ R :=
  ⟨and_intro (and_elim_l' and_elim_l) (and_mono_l and_elim_r),
   and_intro (and_mono_r and_elim_l) (and_elim_r' and_elim_r)⟩

end LTL
