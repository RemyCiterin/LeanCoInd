import Qq
import Lean
import CoInd.M
import CoInd.Paco
import CoInd.Kahn2

universe u₀ u₁ u₂ u₃ u₄

structure IContainer' (I:Type u₀) where
  A: Type u₁
  B: A → Type u₁
  Idx: A → I
  Next : (a: A) → B a → I

namespace IContainer'

variable {I:Type u₀}

-- Obj define an interpretation of the IContainer, and Map allow to map objects using differents universes
def Obj (C:IContainer'.{u₀, u₁} I) (α:I → Type u₂) (i:I) :=
  Σ x:{x: C.A // i = C.Idx x}, ((y: C.B x) → α (C.Next x y))

variable {C:IContainer'.{u₀} I}

def Map {α: I → Type u₃} {β:I → Type u₄} (f:(i:I) → α i → β i) {i:I} : Obj C α i → Obj C β i
| ⟨x, k⟩ => ⟨x, λ y => f (C.Next x y) (k y)⟩

end IContainer'


namespace IContainer'
variable {I:Type u₀}
variable {C:IContainer'.{u₀, u₁} I}

def toContainer (C:IContainer'.{u₀, u₁} I) : Container where
  A := C.A
  B := C.B

#check Container.M C.toContainer

def WellFormedF (C:IContainer'.{u₀} I) :
  (I → Container.M C.toContainer → Prop) →o (I → Container.M C.toContainer → Prop) where
  toFun f i m :=
    C.Idx m.destruct.1 = i ∧ ∀ (x: C.B m.destruct.1), f (C.Next _ x) (m.destruct.2 x)

  monotone' := by
    intro p₁ p₂ h₀ i x ⟨h₁, h₂⟩
    constructor
    · assumption
    · intro y
      apply h₀
      apply h₂

def PWellFormed (p:I → Container.M C.toContainer → Prop) (i:I) (x:Container.M C.toContainer) : Prop :=
  pgfp (WellFormedF C) p i x

def WellFormed (i:I) (x:Container.M C.toContainer) : Prop :=
  PWellFormed ⊥ i x

#check PWellFormed
def WellFormed.corec (P: (i:I) → Container.M C.toContainer → Prop) :
  (∀ i x, P i x → WellFormedF C (P ⊔ PWellFormed P) i x) → ∀ i x, P i x → WellFormed i x := by
  intro h i x
  have := (pgfp.coinduction (WellFormedF C) P).2 h
  apply this

def M (C:IContainer'.{u₀, u₁} I) (i:I) := {m:Container.M C.toContainer // WellFormed i m}

#check M C

#check pgfp.unfold

theorem M.wf_destruct {i:I} : ∀ (m: M C i),
  ∀ x, WellFormed (C.Next m.1.destruct.1 x) (m.1.destruct.2 x) := λ ⟨m, wf⟩ =>
by
  simp only [WellFormed, PWellFormed] at wf
  rw [←pgfp.unfold] at wf
  simp only [CompleteLattice.bot_sup] at wf
  have ⟨_, y⟩ := wf
  exact y

theorem M.index_destruct {i:I} : ∀ (m:M C i), i = C.Idx m.1.destruct.1 := λ ⟨m, wf⟩ =>
by
  simp only [WellFormed, PWellFormed] at wf
  rw [←pgfp.unfold] at wf
  simp only [CompleteLattice.bot_sup] at wf
  have ⟨x, _⟩ := wf
  apply Eq.symm
  exact x


def M.destruct {i:I} : M C i → Obj C (M C) i := λ ⟨m, wf⟩ =>
  let n  := (Container.M.destruct m).1
  let k  := (Container.M.destruct m).2
  ⟨⟨n, by rw [index_destruct ⟨m, wf⟩]⟩, λ x => ⟨k x, by apply M.wf_destruct ⟨m, wf⟩⟩⟩

def Sigma.snd_equals {α:Type _} {β:α → Type _} (x:α) (y z:β x) :
  Sigma.mk x y = Sigma.mk x z → y = z := by
  intro h
  cases h
  rfl

def M.corec.automaton (f:(i:I) → α i → Obj C α i) :
  (Σ i, α i) → (C.toContainer.Obj (Σ i, α i)) :=
  λ ⟨i, x⟩ => ⟨(f i x).1.1, λ y => ⟨_, (f i x).2 y⟩⟩

def M.corec.automaton.wf (f:(i:I) → α i → Obj C α i) :
  ∀ i x, (∃ y, x = Container.M.corec (automaton f) ⟨i, y⟩) → WellFormed i x :=
by
  apply WellFormed.corec (P := _)
  intro i x ⟨y, h₀⟩
  cases h₀
  constructor
  · simp only [Container.M.destruct_corec, Container.Map, automaton]
    have := (f i y).1.2
    rw [←this]
  · intro z
    apply Or.inl
    exists (f _ y).snd _

def M.corec (f:(i:I) → α i → Obj C α i) {i:I} (x₀:α i) : M C i where
  val := Container.M.corec (corec.automaton f) ⟨i, x₀⟩
  property := by
    apply corec.automaton.wf f
    exists x₀

def M.destruct_corec {α: I → Type u₃} (f:(i:I) → α i → Obj C α i) {i:I} (x₀:α i) :
  destruct (corec f x₀) = Map (λ i => @corec I C α f i) (f i x₀) :=
by
  rfl

def M.lift_destruct_eq (i: I) (x : C.toContainer.M) (wf: WellFormed i x) (y: C.Obj C.M i) :
  destruct ⟨x, wf⟩ = y → x.destruct = ⟨y.1.1, λ x => (y.2 x).1⟩ := by
  intro h
  subst h
  rfl



theorem M.bisim (R:(i:I) → M C i → M C i → Prop)
  (h₀: ∀ i x y, R i x y → ∃ node k₁ k₂,
    destruct x = ⟨node, k₁⟩ ∧ destruct y = ⟨node, k₂⟩ ∧
    ∀ z, R _ (k₁ z) (k₂ z)
  )
  {i:I} : ∀ x y, R i x y → x = y :=
by
  intro ⟨x, wfx⟩ ⟨y, wfy⟩ h₁
  suffices h: x = y by
    induction h
    rfl
  apply Container.M.bisim (λ x y => ∃ i, ∃ (wfx: WellFormed i x) (wfy:WellFormed i y), R i ⟨x, wfx⟩ ⟨y, wfy⟩)
  · intro x y ⟨i, wfx, wfy, r⟩
    have ⟨⟨node, h₄⟩, k₁, k₂, h₁, h₂, h₃⟩ := h₀ i ⟨x, wfx⟩ ⟨y, wfy⟩ r
    have h₁ := lift_destruct_eq _ _ _ _ h₁
    have h₂ := lift_destruct_eq _ _ _ _ h₂
    have wfx' := wf_destruct ⟨x, wfx⟩
    have wfy' := wf_destruct ⟨y, wfy⟩

    exists node
    exists λ a => (k₁ a).1
    exists λ x => (k₂ x).1
    simp only [h₁, h₂, true_and]
    intro a
    exists C.Next node a
    simp only [toContainer] at a
    exists (by
        rw [h₁] at wfx'
        apply wfx'
      )
    exists (by
        rw [h₂] at wfy'
        apply wfy'
      )
    exact h₃ a
  exists i
  exists wfx
  exists wfy

end IContainer'
