import CoInd.Container

namespace Container

inductive W (C:Container.{u}) where
| mk: (node:C.A) → (C.B node → W C) → W C

variable {C:Container.{u}}

def W.construct (x:C.Obj (W C)) : W C :=
  .mk x.fst x.snd

def W.recF {α: Type v} (f:C.Obj α → α) : W C → α
| .mk node children =>
  f ⟨node, λ x => recF f <| children x⟩

def W.recF_eq {α:Type v} (f:C.Obj α → α) (x₀: C.Obj (W C)) :
  W.recF f (construct x₀) = f (Map (W.recF f) x₀) := by
  rfl

def W.ind {P: W C → Prop}
  (h: ∀ x:C.Obj (W C), (∀ y, P (x.2 y)) → P (W.construct x))
  : ∀ x, P x := by
  intro x
  induction x with
  | mk n k h' =>
    suffices P (construct ⟨n, k⟩) by
      apply this
    apply h
    intro y
    apply h'

end Container
