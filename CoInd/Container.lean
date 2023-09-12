
universe u₁ u₂ u₃ u₄
structure Container where
  A: Type u₁
  B: A → Type u₁

namespace Container

variable {C:Container.{u₁}}

abbrev Obj (C:Container.{u₁}) (α:Type u₃) :=
  Σ' X:C.A, C.B X → α

def Map {C:Container.{u₁}} {α:Type u₃} {β: Type u₄} (f:α → β) (x:C.Obj α) : C.Obj β :=
  ⟨x.fst, f ∘ x.snd⟩

instance (C:Container) : Functor C.Obj where
  map f x := ⟨x.fst, f ∘ x.snd⟩

def Obj.snd_equals_iff {α:Type u₂} (n:C.A) (kx ky:C.B n → α) :
  (⟨n, kx⟩ : C.Obj α) = ⟨n, ky⟩ ↔ kx = ky := by
  constructor <;> intro h
  . cases h
    rfl
  . cases h
    rfl

end Container


structure IContainer (I:Type u₀) where
  A: I → Type u₀
  B: (i:I) → A i → Type u₀
  N: (i:I) → (a:A i) → B i a → I

namespace IContainer

variable {I:Type u₀}

def Obj (C:IContainer.{u₀} I) (α:I → Type u₃) (i:I) :=
  Σ x:C.A i, ∀ y:C.B i x, α (C.N i x y)

variable {C:IContainer.{u₀} I}

def Map {α: I → Type u₃} {β:I → Type u₄} (f:(i:I) → α i → β i) {i:I} : Obj C α i → Obj C β i
| ⟨x, k⟩ => ⟨x, λ y => f (C.N i x y) (k y)⟩

def Obj.snd_equals_iff {α:I → Type u₂} {i:I} (n:C.A i) (kx ky:∀ y:C.B i n, α (C.N i n y)) :
  (⟨n, kx⟩ : C.Obj α i) = ⟨n, ky⟩ ↔ kx = ky := by
  constructor <;> intro h
  . cases h
    rfl
  . cases h
    rfl

end IContainer


