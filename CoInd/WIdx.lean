import CoInd.Container

namespace IContainer

variable {I:Type u}
variable {C:IContainer I}

inductive W (C:IContainer I) : I → Type u where
| mk: {i:I} → (node:C.A i) → (∀ y:C.B i node, W C (C.N i node y)) → W C i

def W.construct {i:I} (x:C.Obj (W C) i) : W C i :=
  ⟨x.1, x.2⟩

def W.recF {α:I → Type u} (f:(i:I) → C.Obj α i → α i) {i:I} : W C i → α i
| mk node children =>
  f i ⟨node, λ x => recF f <| children x⟩

def W.ind {P: ∀ i, W C i → Prop}
  (h: ∀ i, ∀ x:C.Obj (W C) i, (∀ y, P _ (x.2 y)) → P i (W.construct x))
  : ∀ i x, P i x := by
  intro i x
  induction x with
  | mk n k h' =>
    suffices P _ (construct ⟨n, k⟩) by
      apply this
    apply h
    intro y
    apply h'

end IContainer


