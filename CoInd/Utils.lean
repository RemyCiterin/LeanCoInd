import CoInd.M
import CoInd.MIdx
import CoInd.QPF
import CoInd.Eqns

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

attribute [eqns QPF.M.construct_destruct] M.construct
attribute [eqns QPF.M.destruct_construct QPF.M.destruct_corec] M.destruct

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


attribute [eqns QPF.M.construct_destruct] M.construct
attribute [eqns QPF.M.destruct_construct QPF.M.destruct_corec] M.destruct

#check M.construct
#check M.construct_destruct
#check M.destruct_construct

#check Functor

end IContainer


namespace QPF

variable {F:Type u₁ → Type u₁} [inst:QPF F]
def M.construct.automaton : F (M F) → F (F <| M F) := Functor.map M.destruct

def M.construct (x₀: F (M F)) : M F :=
  M.corec M.construct.automaton x₀

#check M.corec
#check M.construct
def M.construct_def : construct = corec (@construct.automaton F _) := by rfl


theorem M.construct_destruct (x:M F) : construct (destruct x) = x :=
by
  let R (x y: M F) := x = construct (destruct y)
  apply bisim R
  . intro x y h₀
    have h₀ := congrArg destruct h₀
    --rw [h₀]
    simp [liftr]
    simp only [construct, destruct_corec, construct.automaton] at h₀
    exists Functor.map (λ a => ⟨⟨construct <| destruct a, a⟩, by simp⟩) (destruct y)
    rw [h₀]
    constructor
    . simp only [←QPF.map_comp]
      rfl
    . rw [←QPF.M.map_comp]
      have : inst.map id (destruct y) = destruct y := by rw [QPF.map_id]
      apply Eq.trans _ this
      apply congrFun
      funext _
      rfl
  . rfl

def M.destruct_construct : ∀ x: F (M F), destruct (construct x) = x :=
by
  intro x

  simp only [construct]
  rw [destruct_corec]
  conv =>
    lhs
    lhs
    rw [←@construct_def F]
  simp only [construct.automaton]
  rw [←map_comp]
  apply Eq.trans _ (QPF.map_id x)
  conv =>
    lhs
    lhs
    intro x
    simp only [Function.comp, construct_destruct]


attribute [eqns QPF.M.construct_destruct] M.construct
attribute [eqns QPF.M.destruct_construct QPF.M.destruct_corec] M.destruct

#check M.construct
#check M.construct_destruct
#check M.destruct_construct

example : ∀ x:M F, M.construct (M.destruct x) = x := by
  intro x
  simp [M.construct]



end QPF
