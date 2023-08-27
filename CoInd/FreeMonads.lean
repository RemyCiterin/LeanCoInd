import CoInd.M
import CoInd.Utils
--import LustreDSL.Paco

-- definition of free monads to represent impure programs

universe u₁ u₂ u₃ u₄ u₅

section


#check Container
variable (C:_root_.Container.{u₁, u₂})
variable (R:Type u₃)

inductive Free.A  where
| Pure : R → Free.A
| Free : C.A → Free.A

def Free.B : Free.A C R → Type _
| .Pure _ => PEmpty
| .Free node => C.B node

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

variable {C:_root_.Container.{u₁, u₂}}

def Free.Map {R:Type u₃} {α:Type u₄} {β:Type u₅} (f:α → β) : Free.Functor C R α → Free.Functor C R β
| .Pure r => .Pure r
| .Free node k => .Free node <| f ∘ k

def Free.hom {R:Type u₃} {α:Type u₄} : (Free.Container C R).Obj α → Free.Functor C R α
| ⟨.Pure x, _⟩ => .Pure x
| ⟨.Free n, k⟩ => .Free n k

def Free.inv {R:Type u₃} {α:Type u₄} : Free.Functor C R α → (Free.Container C R).Obj α
| .Pure x => ⟨.Pure x, λ e => e.casesOn⟩
| .Free n k => ⟨.Free n, k⟩

@[simp] def Free.inv_hom {R:Type u₃} {α:Type u₄} : ∀ x:(Free.Container C R).Obj α, inv (hom x) = x := by
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

@[simp] def Free.hom_inv {R:Type u₃} {α:Type u₄} (x: Free.Functor C R α) : hom (inv x) = x := by
  cases x <;> simp [inv, hom]

@[simp] def Free.hom_map {R:Type u₃} {α:Type u₄} {β:Type u₅} (f:α → β) : ∀ x:(Free.Container C R).Obj α,
  hom (Container.Map f x) = Map f (hom x) := by
  intro ⟨n, k⟩
  cases n <;> simp [Map, hom, inv, Container.Map]

def Free.destruct {R:Type u₃} (f:Free C R) : Free.Functor C R (Free C R) :=
  Free.hom (M.destruct f)

def Free.corec {R:Type u₃} {α:Type u₄} (f:α → Free.Functor C R α) (x₀:α) : Free C R :=
  M.corec (λ x => Free.inv (f x)) x₀

def Free.construct {R:Type u₃} (f:Free.Functor C R (Free C R)) : Free C R :=
  M.construct (inv f)

def Free.destruct_corec {R:Type u₃} {α:Type u₄} (f:α → Free.Functor C R α) (x₀:α) :
  Free.destruct (Free.corec f x₀) = Free.Map (Free.corec f) (f x₀) :=
by
  simp [destruct, corec]
  rw [M.destruct_corec]
  generalize f x₀ = x
  cases x <;> simp [hom, inv, Container.Map, Map]

def Free.construct_destruct {R:Type u₃} (f:Free C R) : construct (destruct f) = f :=
by
  simp [construct, destruct, M.construct_destruct]

def Free.destruct_construct {R:Type u₃} (f:Functor C R (Free C R)) : destruct (construct f) = f := by
  simp [construct, destruct, M.destruct_construct]

def Free.pure {R:Type u₃} (x:R) : Free C R := construct (Functor.Pure x)

def Free.bind.automaton {R S:Type u₃} (f:R → Free C S) : Free C R ⊕ Free C S → Functor C S (Free C R ⊕ Free C S)
| .inr x => Map .inr (destruct x)
| .inl x => match destruct x with
  | .Pure r => Map .inr <| destruct <| f r
  | .Free n k => .Free n (.inl ∘ k)

def Free.bind {R S:Type u₃}
  (x:Free C R) (f:R → Free C S) : Free C S :=
  @corec C S (Free C R ⊕ Free C S) (bind.automaton f) (.inl x)

instance : Monad (Free C) where
  pure := Free.pure
  bind := Free.bind

def Free.trigger (node: C.A) : Free C (C.B node) :=
  construct (.Free node pure)


end
