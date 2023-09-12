import CoInd.Container
import CoInd.QPF.Basics
import CoInd.QPF.M
import CoInd.Eqns

import CoInd.Utils

inductive Free.FreeF (F:Type u → Type u) [QPF F] (R:Type u) (α:Type u) where
| Pure : R → FreeF F R α
| Free : F α → FreeF F R α

-- M F ≈ F (M F)
-- (α -> F (Free F α)) -> α → M F
-- cofix f x ≈ map (cofix f) (f x)
-- done : M F -> Free F α
-- F α = Cons Nat α
-- cofix (λ x => if x > 100 then done (repeat x) else Cons x (Cons x (pure (x+1)))) 0


inductive Free.A (F:Type u → Type u) [inst:QPF F] (R:Type u) where
| Pure: R → A F R
| Free: inst.C.A → A F R

def Free.B (F:Type u → Type u) [inst:QPF F] (R:Type u) : Free.A F R → Type u
| .Pure _ => PEmpty
| .Free x => inst.C.B x

variable {F:Type u → Type u} [inst:QPF F]

instance Free.QPFinst {R:Type u} : QPF (Free.FreeF F R) where
  map f
  | .Pure r => .Pure r
  | .Free x => .Free <| f <$> x

  C := ⟨Free.A F R, Free.B F R⟩

  abs
  | ⟨.Pure r, _⟩ => .Pure r
  | ⟨.Free x, k⟩ => Free.FreeF.Free <| inst.abs ⟨x, k⟩

  repr
  | .Pure r => ⟨.Pure r, λ e => e.elim⟩
  | .Free x => ⟨.Free (inst.repr x).1, (inst.repr x).2⟩

  abs_repr := by
    intro α x
    cases x with
    | Pure r =>
      simp only
    | Free x =>
      have : (⟨(inst.repr x).1, (inst.repr x).2⟩ : inst.C.Obj α) = inst.repr x := by
        rfl
      simp only
      rw [this, inst.abs_repr]

  abs_map := by
    intro α β f x
    cases x with | mk n k =>
    cases n with
    | Pure r =>
      simp [Container.Map]
    | Free x =>
      simp [Container.Map, ←inst.abs_map]

#check λ R => @QPF.M.bisim (Free.FreeF F R) inferInstance
#print QPF.M.liftr


def Free (F:Type u → Type u) [QPF F] (R:Type u) := QPF.M (Free.FreeF F R)

def Free.construct {R:Type u} (x: FreeF F R (Free F R)) : Free F R :=
  QPF.M.construct x

def Free.destruct {R:Type u} (x:Free F R) : FreeF F R (Free F R) :=
  QPF.M.destruct x

def Free.corec {R α:Type u} (f:α → FreeF F R α) : α → Free F R :=
  QPF.M.corec f


def Free.construct_destruct {R:Type u} (x:Free F R) : construct (destruct x) = x := by rw [construct, destruct, QPF.M.construct]
def Free.destruct_construct {R:Type u} (x:FreeF F R <| Free F R) : destruct (construct x) = x := by rw [construct, destruct, QPF.M.destruct]
def Free.destruct_corec {R:Type u} (f:α → FreeF F R α) (x:α) : destruct (corec f x) = corec f <$> f x := by rw [corec, destruct, QPF.M.destruct]

attribute [eqns Free.construct_destruct] Free.construct
attribute [eqns Free.destruct_construct Free.destruct_corec] Free.destruct


@[simp] instance : Coe (Free.FreeF F R (Free F R)) (Free F R) := ⟨Free.construct⟩
@[simp] instance : Coe (Free F R) (Free.FreeF F R (Free F R)) := ⟨Free.destruct⟩

def Free.bind.automaton {R S:Type u} (k:R → Free F S) : Free F R ⊕ Free F S → FreeF F S (Free F R ⊕ Free F S)
| .inl x => match destruct x with
  | .Pure x => .inr <$> destruct (k x)
  | .Free f => .Free <| .inl <$> f
| .inr y =>
  .inr <$> destruct y

instance Free.Monad : Monad (Free F) where
  bind x k := Free.corec (Free.bind.automaton k) (.inl x)
  pure r := Free.construct <| .Pure r

def Free.free {R:Type u} (f:F (Free F R)) : Free F R := construct (.Free f)


@[eliminator] theorem Free.by_cases {motive:Free F R → Sort _} (pure:∀ r:R, motive (pure r)) (free:∀ f:F (Free F R), motive (free f)) : ∀ x, motive x := by
  intro x
  rw [←construct_destruct x]
  cases destruct x with
  | Pure r =>
    exact pure r
  | Free f =>
    exact free f

#print QPF.M.liftr

theorem Free.bind_inr.internal {R S:Type u} (k:R → Free F S) : ∀ x y, (corec (bind.automaton k) (.inr x) = y) → x = y :=
by
  apply QPF.M.bisim (λ x y => corec (bind.automaton k) (.inr x) = y)
  . intro x y h₁
    induction h₁
    rw [corec, QPF.M.destruct_corec]
    conv =>
      congr
      . skip
      . skip
      . rhs
        simp only [bind.automaton]
    exists (λ x => ⟨⟨x, corec (bind.automaton k) (.inr x)⟩, by rfl⟩) <$> destruct x
    rw [destruct]
    constructor
    . simp only [←QPF.map_comp, Function.comp]
      apply Eq.trans _ (QPF.map_id _)
      rfl
    . simp only [←QPF.map_comp, Function.comp]
      rfl

theorem Free.bind_inr {R S:Type u} (k:R → Free F S) : ∀ x, corec (bind.automaton k) (.inr x) = x := by
  intro x
  have := Free.bind_inr.internal k x (corec (bind.automaton k) (.inr x)) (by rfl)
  conv =>
    rhs
    rw [this]

@[simp] theorem Free.pure_bind {R S:Type u} (x:R) (k:R → Free F S) : bind (pure x) k = k x := by
  simp only [pure, bind]
  conv =>
    lhs
    rw [←construct_destruct (corec (bind.automaton k) (.inl (construct <| .Pure x)))]
    rw [destruct_corec]
    rhs
    rhs
    simp only [bind.automaton, destruct_construct]
  simp only [←QPF.map_comp, Function.comp]
  conv =>
    lhs
    congr
    lhs
    intro x
    rw [bind_inr]
  have := QPF.map_id (destruct (k x))
  simp only [id] at this
  rw [this, construct_destruct]

#check flip
@[simp] theorem Free.free_bind {R S:Type u} (f:F (Free F R)) (k:R → Free F S) : bind (free f) k = free (flip bind k <$> f) := by
  simp only [free, bind, flip]
  conv =>
    lhs
    rw [←construct_destruct (corec (bind.automaton k) (.inl (construct <| .Free f)))]
    rw [destruct_corec]
    rhs
    rhs
    simp only [bind.automaton, destruct_construct]
  apply congrArg
  simp only [Functor.map, ←QPF.map_comp, Function.comp]

theorem Free.bind_pure.internal {R:Type u} : ∀ x y:Free F R, bind x pure = y → x = y := by
  apply QPF.M.bisim
  intro x y h₁
  induction h₁
  exists (λ x => ⟨(x, bind x Free.Monad.pure), by rfl⟩) <$> destruct x
  cases x using by_cases with
  | pure r =>
    have : destruct (pure r) = .Pure r := by
      exact @destruct_construct F _ R (FreeF.Pure r)
    simp only [Functor.map, this, pure_bind r]
    constructor <;> rfl
  | free f =>
    have : destruct (free f) = .Free f := by
      exact @destruct_construct F _ R (FreeF.Free f)
    simp only [Functor.map, this, free_bind, ←QPF.map_comp, Function.comp]
    constructor
    . conv =>
        rhs
        congr
        rw [←QPF.map_id f]
      rw [free, construct, QPF.M.destruct_construct]
      rfl
    . simp only [free, construct, QPF.M.destruct_construct]
      rfl

@[simp] theorem Free.bind_pure {R:Type u} (x:Free F R) : bind x pure = x := by
  conv =>
    rhs
    rw [bind_pure.internal x (bind x pure)]
    rfl
    rfl

inductive Free.eq {R:Type u} (aux:Free F R → Free F R → Prop) : Free F R → Free F R → Prop where
| Pure : (r:R) → Free.eq aux (pure r) (pure r)
| Free : (f₁ f₂:F (Free F R)) → QPF.M.liftr F aux f₁ f₂ → Free.eq aux (free f₁) (free f₂)

def Free.bisim {R:Type u} (r:Free F R → Free F R → Prop)
  (h₀:∀ x y, r x y → Free.eq r x y) : ∀ x y, r x y → x = y := by
  apply QPF.M.bisim
  intro x y h₁
  have h₁ := h₀ _ _ h₁
  cases h₁ with
  | Pure r =>
    exists .Pure r
  | Free f₁ f₂ h =>
    have ⟨z, h⟩ := h
    exists .Free z
    simp only [free, construct, QPF.M.destruct_construct, Functor.map, FreeF.Free.injEq]
    exact h

theorem Free.bind_bind.internal {R S T:Type u} (k₁:R → Free F S) (k₂:S → Free F T) :
  ∀ y z, (∃ x, bind (bind x k₁) k₂ = y ∧  bind x (flip bind k₂ ∘ k₁) = z) → y = z := by
  apply Free.bisim
  intro y z ⟨x, h₁, h₂⟩
  induction h₁
  induction h₂
  sorry
