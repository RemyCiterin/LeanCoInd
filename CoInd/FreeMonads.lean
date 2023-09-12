import CoInd.M
import CoInd.Utils
--import LustreDSL.Paco

-- definition of free monads to represent impure programs

universe u₁ u₂ u₃ u₄ u₅

section


#check Container
variable (C:_root_.Container.{u₁})
variable (R:Type u₁)

inductive Free.A  where
| Pure : R → Free.A
| Free : C.A → Free.A

def Free.B : Free.A C R → Type _
| .Pure _ => PEmpty
| .Free node => C.B node

#check Free.A
#check Free.B

def Free.Container : Container where
  A := Free.A C R
  B := Free.B C R

inductive Free.Functor (α: Type u₄) where
| Pure : R → Functor α
| Free : (node:C.A) → (C.B node → α) → Functor α

-- I dont use Functor because of universe polymorphism
#check Container.M

def Free := Container.M (Free.Container C R)

end

section
open Container

variable {C:_root_.Container.{u₁}}

def Free.Map {R:Type u₁} {α:Type u₄} {β:Type u₅} (f:α → β) : Free.Functor C R α → Free.Functor C R β
| .Pure r => .Pure r
| .Free node k => .Free node <| f ∘ k

def Free.hom {R:Type u₁} {α:Type u₄} : (Free.Container C R).Obj α → Free.Functor C R α
| ⟨.Pure x, _⟩ => .Pure x
| ⟨.Free n, k⟩ => .Free n k

def Free.inv {R:Type u₁} {α:Type u₄} : Free.Functor C R α → (Free.Container C R).Obj α
| .Pure x => ⟨.Pure x, λ e => e.casesOn⟩
| .Free n k => ⟨.Free n, k⟩

@[simp] def Free.inv_hom {R:Type u₁} {α:Type u₄} : ∀ x:(Free.Container C R).Obj α, inv (hom x) = x := by
  intro ⟨n, k⟩
  cases n with
  | Pure r =>
    simp only [inv, hom]
    have : k = λ e => e.casesOn := by
      funext x
      cases x
    rw [this]
  | Free n =>
    simp only [inv, hom]

@[simp] def Free.hom_inv {R:Type u₁} {α:Type u₄} (x: Free.Functor C R α) : hom (inv x) = x := by
  cases x <;> simp [inv, hom]

@[simp] def Free.hom_map {R:Type u₁} {α:Type u₄} {β:Type u₅} (f:α → β) : ∀ x:(Free.Container C R).Obj α,
  hom (Container.Map f x) = Map f (hom x) := by
  intro ⟨n, k⟩
  cases n <;> simp [Map, hom, inv, Container.Map]

def Free.destruct {R:Type u₁} (f:Free C R) : Free.Functor C R (Free C R) :=
  Free.hom (M.destruct f)

def Free.corec {R:Type u₁} {α:Type u₄} (f:α → Free.Functor C R α) (x₀:α) : Free C R :=
  M.corec (λ x => Free.inv (f x)) x₀

def Free.construct {R:Type u₁} (f:Free.Functor C R (Free C R)) : Free C R :=
  M.construct (inv f)

def Free.destruct_corec {R:Type u₁} {α:Type u₄} (f:α → Free.Functor C R α) (x₀:α) :
  Free.destruct (Free.corec f x₀) = Free.Map (Free.corec f) (f x₀) :=
by
  simp [destruct, corec]
  rw [M.destruct_corec]
  generalize f x₀ = x
  cases x <;> simp [hom, inv, Container.Map, Map]

def Free.construct_destruct {R:Type u₁} (f:Free C R) : construct (destruct f) = f :=
by
  simp [construct, destruct, M.construct_destruct]

def Free.destruct_construct {R:Type u₁} (f:Functor C R (Free C R)) : destruct (construct f) = f := by
  simp [construct, destruct, M.destruct_construct]

inductive Free.equivF {R S:Type u₁} (equiv:R → S → Prop) (aux:Free C R → Free C S → Prop) : Free C R → Free C S →  Prop where
| Pure : ∀ (r:R) (s:S), equiv r s → equivF equiv aux (construct <| .Pure r) (construct <| .Pure s)
| Free : (node:C.A) → (k₁:C.B node → Free C R) → (k₂:C.B node → Free C S) → (∀ x:C.B node, aux (k₁ x) (k₂ x)) →
  equivF equiv aux (construct <| .Free node k₁) (construct <| .Free node k₂)

def Free.equivF' {R S:Type u₁} (equiv:R → S → Prop) : (Free C R → Free C S → Prop) →o (Free C R → Free C S → Prop) where
  toFun := equivF equiv
  monotone' := by
    intro p q h₀ x y h₁
    cases h₁ with
    | Pure r s h₁ =>
      apply equivF.Pure _ _ h₁
    | Free node k₁ k₂ h₁ =>
      apply equivF.Free
      intro x
      apply h₀
      apply h₁

def Free.pequiv {R S:Type u₁} (equiv: R → S → Prop) (p:Free C R → Free C S → Prop) : Free C R → Free C S → Prop :=
  pgfp (equivF' equiv) p

def Free.equiv {R S:Type u₁} (equiv: R → S → Prop) : Free C R → Free C S → Prop :=
  pequiv equiv ⊥

def Free.eq {R:Type u₁} := @Free.equiv C R R Eq

theorem Free.equiv.coinduction {R S:Type u₁} (eq:R → S → Prop) (P:Free C R → Free C S → Prop) :
  (∀ x y, P x y → equivF eq (P ⊔  pequiv eq P) x y) → ∀ x y, P x y → equiv eq x y := by
  intro h x y h'
  apply (pgfp.coinduction (equivF' eq) P).2
  apply h
  apply h'

theorem Free.eq.bisim {R:Type u₁}:
  ∀ (x y:Free C R), Free.eq x y → x = y := by
  apply M.bisim
  intro x y h₁
  simp [eq, equiv, pequiv] at h₁
  rw [←pgfp.unfold] at h₁
  cases h₁ with
  | Pure x y h₁ =>
    induction h₁
    exists (A.Pure x)
    exists (λ e => e.casesOn)
    exists (λ e => e.casesOn)
    simp only [construct, M.destruct_construct, inv, true_and]
    intro x
    apply x.elim
  | Free node k₁ k₂ h =>
    exists (A.Free node)
    exists k₁
    exists k₂
    simp only [construct, M.destruct_construct, inv, true_and]
    intro x
    rw [CompleteLattice.bot_sup] at h
    apply h


theorem Free.eq.rfl {R:Type u₁} : ∀ (x:Free C R), eq x x := by
  have : ∀ (x y:Free C R), x = y → Free.eq x y := by
    apply Free.equiv.coinduction
    intro x y h
    cases h
    conv =>
      congr
      . rfl
      . rfl
      . rw [←construct_destruct x]
      . rw [←construct_destruct x]
    cases destruct x with
    | Pure r =>
      apply equivF.Pure
      rfl
    | Free node k =>
      apply equivF.Free
      intro y
      left
      rfl
  intro x
  apply this
  rfl

def Free.pure {R:Type u₁} (x:R) : Free C R := construct (Functor.Pure x)

def Free.bind.automaton {R S:Type u₁} (f:R → Free C S) : Free C R ⊕ Free C S → Functor C S (Free C R ⊕ Free C S)
| .inr x => Map .inr (destruct x)
| .inl x => match destruct x with
  | .Pure r => Map .inr <| destruct <| f r
  | .Free n k => .Free n (.inl ∘ k)

def Free.bind {R S:Type u₁}
  (x:Free C R) (f:R → Free C S) : Free C S :=
  @corec C S (Free C R ⊕ Free C S) (bind.automaton f) (.inl x)

#print Lean.Meta.Simp.Config

theorem Free.bind_inr {R S:Type u₁} (f:R → Free C S) (x:Free C S) :
  corec (bind.automaton f) (.inr x) = x := by
  apply Free.eq.bisim
  have : ∀ x y, x = corec (bind.automaton f) (.inr y) → eq x y := by
    apply Free.equiv.coinduction
    intro x y h₁
    conv =>
      congr
      . rfl
      . rfl
      . rw [←construct_destruct x]
      . rw [←construct_destruct y]
    have h₂ := congrArg destruct h₁
    clear h₁
    rw [destruct_corec] at h₂
    cases hy: destruct y with
    | Pure r =>
      simp only [Map, hy, bind.automaton] at h₂
      rw [h₂]
      apply equivF.Pure
      rfl
    | Free n k =>
      simp only [Map, bind.automaton, hy] at h₂
      rw [h₂]
      apply equivF.Free
      intro y
      left
      rfl
  apply this
  rfl

theorem Free.bind_pure {R S:Type u₁} (r:R) (k:R → Free C S) :
  bind (pure r) k = k r := by
  rw [←construct_destruct <| k r]
  rw [←construct_destruct <| bind (pure r) k]
  simp only [bind, pure, destruct_corec]
  apply congrArg construct
  conv =>
    lhs
    congr
    . rfl
    . simp only [bind.automaton, destruct_construct]
  cases destruct (k r) with
  | Pure r =>
    simp only [Map]
  | Free n k =>
    simp only [Map]
    conv =>
      lhs
      congr
      simp only [Function.comp]
      intro x
      rw [bind_inr]

instance : Monad (Free C) where
  pure := Free.pure
  bind := Free.bind

#check λ R (r:R) => (pure r:Free C R) >>= pure

def Free.trigger (node: C.A) : Free C (C.B node) :=
  construct (.Free node pure)


end
