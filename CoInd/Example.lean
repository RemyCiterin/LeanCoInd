import CoInd.QPF.FreeMonads
import CoInd.QPF.Basics
import CoInd.Container
import CoInd.Utils
import CoInd.QPF.M

inductive List.F (α: Type u) (β: Type u) where
| Nil : F α β
| Cons : α × β → F α β

inductive List.A (α: Type u) where
| Nil : A α
| Cons : α → A α

def List.B (α: Type u) : A α → Type u
| .Nil => PEmpty
| .Cons _ => PUnit

-- We prove that List.F is a quotient of a polynomial functor
instance (α: Type u) : QPF (List.F α) where
  map f
  | .Nil => .Nil
  | .Cons (x, y) => .Cons (x, f y)

  C := ⟨List.A α, List.B α⟩

  abs
  | ⟨.Nil, _⟩ => .Nil
  | ⟨.Cons x, k⟩ => .Cons (x, k PUnit.unit)

  repr
  | .Nil => ⟨.Nil, λ e => e.elim⟩
  | .Cons ⟨x, y⟩ => ⟨.Cons x, λ _ => y⟩

  abs_repr := by
    intro β x
    cases x with
    | Nil =>
      simp only
    | Cons x =>
      simp only

  abs_map := by
    intro β γ f x
    cases x with
    | mk l r =>
      cases l with
      | Nil =>
        simp only [Container.Map]
      | Cons x =>
        simp [Container.Map]

abbrev FreeList (α β: Type u) := Free (List.F α) β

def prog : FreeList Nat Nat := do
  let l ← Free.free .Nil
  Free.free <| .Cons (1, l)



