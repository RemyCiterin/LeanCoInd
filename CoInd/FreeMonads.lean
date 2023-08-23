import CoInd.M
--import LustreDSL.Paco

-- definition of free monads to represent impure programs

universe u₁ u₂ u₃ u₄ u₅

section

variable (E:Type u₁ → Type u₂) (R:Type u₃)

inductive Free.A  where
| Pure : R → Free.A
| Free : (X:Type u₁) → E X → Free.A

def Free.B : Free.A E R → Type _
| .Pure _ => PEmpty
| .Free X _ => X

def Free.Container : Container where
  A := Free.A E R
  B := Free.B E R

inductive Free.Functor (α: Type u₄) where
| Pure : R → Functor α
| Free : (X:Type u₁) → E X → (X → α) → Functor α

-- I dont use Functor because of universe polymorphism
#check Container.M

def Free := Container.M (Free.Container E R)

end

section
open Container

variable {E:Type u₁ → Type u₂}

def Free.Map {R:Type u₃} {α:Type u₄} {β:Type u₅} (f:α → β) : Free.Functor E R α → Free.Functor E R β
| .Pure r => .Pure r
| .Free X e k => .Free X e <| f ∘ k

def Free.hom {R:Type u₃} {α:Type u₄} : (Free.Container E R).Obj α → Free.Functor E R α
| ⟨.Pure x, _⟩ => .Pure x
| ⟨.Free X e, k⟩ => .Free X e k

def Free.inv {R:Type u₃} {α:Type u₄} : Free.Functor E R α → (Free.Container E R).Obj α
| .Pure x => ⟨.Pure x, λ e => e.casesOn⟩
| .Free X e k => ⟨.Free X e, k⟩

@[simp] def Free.inv_hom {R:Type u₃} {α:Type u₄} (x:(Free.Container E R).Obj α) : inv (hom x) = x := by
  cases x with
  | mk n k =>
    cases n with
    | Pure r =>
      simp only [inv, hom]
      have : k = λ e => e.casesOn := by
        funext x
        cases x
      rw [this]
    | Free X e =>
      simp only [inv, hom]

@[simp] def Free.hom_inv {R:Type u₃} {α:Type u₄} (x: Free.Functor E R α) : hom (inv x) = x := by
  cases x with
  | Pure r =>
    simp [inv, hom]
  | Free X e k =>
    simp [inv, hom]

def Free.destruct {R:Type u₃} (f:Free E R) : Free.Functor E R (Free E R) :=
  Free.hom (M.destruct f)

def Free.corec {R:Type u₃} {α:Type u₄} (f:α → Free.Functor E R α) (x₀:α) : Free E R :=
  M.corec (λ x => Free.inv (f x)) x₀

def Free.construct {R:Type u₃} (f:Free.Functor E R (Free E R)) : Free E R :=
  M.construct (inv f)

def Free.destruct_corec {R:Type u₃} {α:Type u₄} (f:α → Free.Functor E R α) (x₀:α) :
  Free.destruct (Free.corec f x₀) = Free.Map (Free.corec f) (f x₀) :=
by
  simp [destruct, corec]
  rw [M.destruct_corec]
  generalize f x₀ = x
  cases x with
  | Pure r =>
    simp [hom, inv, Container.Map, Map]
  | Free X e k =>
    simp [hom, inv, Container.Map, Map]

def Free.construct_destruct {R:Type u₃} (f:Free E R) : construct (destruct f) = f :=
by
  simp [construct, destruct, M.construct_destruct]

def Free.destruct_construct {R:Type u₃} (f:Functor E R (Free E R)) : destruct (construct f) = f := by
  simp [construct, destruct, M.destruct_construct]

end
