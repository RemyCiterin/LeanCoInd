import CoInd.M
import CoInd.MIdx

namespace Container

variable {C:Container.{u₁}}
def M.construct.automaton : C.Obj (M C) → C.Obj (C.Obj <| M C) := Map destruct

def M.construct (x₀: C.Obj (M C)) : M C :=
  M.corec M.construct.automaton x₀

def M.construct_def : construct = corec (@construct.automaton C) := by rfl

theorem M.construct_destruct (x:M C) : construct (destruct x) = x :=
by
  let R (x y: M C) := x = construct (destruct y)
  apply bisim R
  . intro x y h₀
    have h₀ := congrArg destruct h₀
    cases h₁:destruct y
    case mk node k₂ =>
      rw [h₁] at h₀
      simp only [construct, destruct_corec, Map] at h₀
      simp only [construct.automaton, Map] at h₀
      exists node
      exists construct ∘ destruct ∘ k₂
      exists k₂
      constructor
      . exact h₀
      . constructor
        . rfl
        . intro i
          rfl
  . rfl

def M.destruct_construct : ∀ x: C.Obj (M C), destruct (construct x) = x :=
by
  intro ⟨n, k⟩
  --simp only [construct, construct.automaton]
  have : (destruct (construct ⟨n, k⟩)).fst = n := by
    rfl

  simp only [construct]
  rw [destruct_corec construct.automaton ⟨n, k⟩]
  simp only [←construct_def]
  simp only [construct.automaton, Map]

  have : construct ∘ destruct ∘ k = k := by
    funext x
    simp only [Function.comp]
    rw [M.construct_destruct]

  rw [this]


#check M.construct
#check M.construct_destruct
#check M.destruct_construct


end Container


namespace IContainer

variable {I:Type u₀}
variable {C:IContainer.{u₀} I}

#check Map
#check M.destruct

def M.construct.automaton (i:I) : C.Obj (M C) i → C.Obj (C.Obj (M C)) i := Map (@destruct I C)

def M.construct {i:I} (x₀: C.Obj (M C) i) : M C i :=
  M.corec M.construct.automaton x₀

def M.construct_def {i:I} : @construct I C i = corec (@construct.automaton I C) := by rfl


theorem M.construct_destruct {i:I} (x:M C i) : construct (destruct x) = x :=
by
  let R i (x y: M C i) := x = construct (destruct y)
  apply bisim R
  . intro i x y h₀
    have h₀ := congrArg destruct h₀
    cases h₁:destruct y
    case mk node k₂ =>
      rw [h₁] at h₀
      simp only [construct, destruct_corec, Map] at h₀
      simp only [construct.automaton, Map] at h₀
      exists node
      exists λ (x:B C i node) => construct <| destruct <| k₂ x
      exists k₂
      constructor
      . exact h₀
      . constructor
        . rfl
        . intro i
          rfl
  . rfl


def M.destruct_construct {i:I} : ∀ x: C.Obj (M C) i, destruct (construct x) = x :=
by
  intro ⟨n, k⟩
  --simp only [construct, construct.automaton]
  have : (destruct (construct ⟨n, k⟩)).fst = n := by
    rfl

  simp only [construct]
  rw [destruct_corec construct.automaton ⟨n, k⟩]
  simp only [←construct_def]
  simp only [construct.automaton, Map]

  have : (λ x : B C i n => construct <| destruct <| k x) = k := by
    funext x
    simp only [Function.comp]
    rw [M.construct_destruct]

  rw [this]

#check M.construct
#check M.construct_destruct
#check M.destruct_construct

#check Functor

end IContainer

