import CoInd.M
import CoInd.Paco

universe u₀ u₁ u₂ u₃ u₄ u₅


structure IContainer (I:Type u₀) where
  A: I → Type u₁
  B: (i:I) → A i → Type u₂
  N: (i:I) → (a:A i) → B i a → I

namespace IContainer

variable {I:Type u₀}

def Obj (C:IContainer.{u₀, u₁, u₂} I) (α:I → Type u₃) (i:I) :=
  Σ x:C.A i, ∀ y:C.B i x, α (C.N i x y)

def toContainer (C:IContainer.{u₀, u₁, u₂} I) : Container where
  A := Σ i:I, C.A i
  B := λ ⟨i, a⟩ => C.B i a

def WellFormedF (C:IContainer.{u₀, u₁, u₂} I) :
  (I → Container.M C.toContainer → Prop) →o (I → Container.M C.toContainer → Prop) where
  toFun f i m :=
    m.destruct.1.1 = i ∧ ∀ x, f (C.N m.destruct.1.1 m.destruct.1.2 x) (m.destruct.2 x)

  monotone' := by
    intro p₁ p₂ h₀ i x ⟨h₁, h₂⟩
    constructor
    . assumption
    . intro y
      apply h₀
      apply h₂

variable {C:IContainer.{u₀, u₁, u₂} I}

def Map {α: I → Type u₃} {β:I → Type u₄} (f:(i:I) → α i → β i) {i:I} : Obj C α i → Obj C β i
| ⟨x, k⟩ => ⟨x, λ y => f (C.N i x y) (k y)⟩

#check WellFormedF

def PWellFormed (p:I → Container.M C.toContainer → Prop) (i:I) (x:Container.M C.toContainer) : Prop :=
  pgfp (WellFormedF C) p i x

def WellFormed (i:I) (x:Container.M C.toContainer) : Prop :=
  PWellFormed ⊥ i x

def M (C:IContainer.{u₀, u₁, u₂} I) (i:I) := {m:Container.M C.toContainer // WellFormed i m}

#check pgfp.unfold

theorem M.wf_destruct {i:I} : ∀ (m: M C i),
  ∀ x, WellFormed (C.N _ (Container.M.destruct m.1).1.2 x) ((Container.M.destruct m.1).2 x) := λ ⟨m, wf⟩ =>
by
  simp only [WellFormed, PWellFormed] at wf
  rw [←pgfp.unfold] at wf
  simp only [CompleteLattice.bot_sup] at wf
  have ⟨_, y⟩ := wf
  exact y

theorem M.index_destruct {i:I} : ∀ (m:M C i), i = (Container.M.destruct m.1).1.1 := λ ⟨m, wf⟩ =>
by
  simp only [WellFormed, PWellFormed] at wf
  rw [←pgfp.unfold] at wf
  simp only [CompleteLattice.bot_sup] at wf
  have ⟨x, _⟩ := wf
  apply Eq.symm
  exact x


def M.destruct {i:I} : M C i → Obj C (M C) i := λ ⟨m, wf⟩ =>
  let i' := (Container.M.destruct m).1.1
  let n  := (Container.M.destruct m).1.2
  let k  := (Container.M.destruct m).2

  have m' : Obj C (M C) i' :=
    ⟨n, λ x => ⟨k x, by apply M.wf_destruct ⟨m, wf⟩⟩⟩

  cast (by rw [index_destruct ⟨m, wf⟩]) m'

def Sigma.snd_equals {α:Type _} {β:α → Type _} (x:α) (y z:β x) :
  Sigma.mk x y = Sigma.mk x z → y = z := by
  intro h
  cases h
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
  . intro x y ⟨i, wfx, wfy, r⟩
    have ⟨node, k₁, k₂, h₁, h₂, h₃⟩ := h₀ i ⟨x, wfx⟩ ⟨y, wfy⟩ r

    let ix := (Container.M.destruct x).1.1
    let nx := (Container.M.destruct x).1.2
    let kx := (Container.M.destruct x).2

    let iy := (Container.M.destruct y).1.1
    let ny := (Container.M.destruct y).1.2
    let ky := (Container.M.destruct y).2

    --have ⟨hix, wfx⟩ := wfx
    --have ⟨hiy, wfy⟩ := wfy
    have hix := index_destruct ⟨x, wfx⟩
    have hiy := index_destruct ⟨y, wfy⟩
    have wfx' : ∀ a:B C ix nx, WellFormed (C.N ix nx a) (kx a) := wf_destruct ⟨x, wfx⟩
    have wfy' : ∀ a:B C iy ny, WellFormed (C.N iy ny a) (ky a) := wf_destruct ⟨y, wfy⟩
    simp only at hix hiy wfx wfy

    exists ⟨_, node⟩
    exists λ x => (k₁ x).1
    exists λ x => (k₂ x).1
    constructor
    . cases hix
      have hnx: nx = node := by
        apply congrArg Sigma.fst h₁
      cases hnx
      have h₁ := Sigma.snd_equals _ _ _ h₁
      rw [← h₁]
      rfl
    . constructor
      . cases hiy
        have hny: ny = node := by
          apply congrArg Sigma.fst h₂
        cases hny
        have h₂ := Sigma.snd_equals _ _ _ h₂
        rw [← h₂]
        rfl
      . intro a
        exists C.N i node a
        simp only [toContainer] at a
        exists (by
            cases hix
            have : nx = node := by
              apply congrArg Sigma.fst h₁
            cases this
            have h₁ := Sigma.snd_equals _ _ _ h₁
            have wfx' := wfx' a
            cases h₁
            exact wfx'
          )
        exists (by
            cases hiy
            have : ny = node := by
              apply congrArg Sigma.fst h₂
            cases this
            have h₂ := Sigma.snd_equals _ _ _ h₂
            have wfy' := wfy' a
            cases h₂
            exact wfy'
          )

        exact h₃ a
  exists i
  exists wfx
  exists wfy

def M.corec.automaton (f:(i:I) → α i → Obj C α i) :
  (Σ i, α i) → (C.toContainer.Obj (Σ i, α i)) :=
  λ ⟨i, x⟩ => ⟨⟨i, (f i x).1⟩, λ y => ⟨_, (f i x).2 y⟩⟩


def M.corec.automaton.wf (f:(i:I) → α i → Obj C α i) :
  (λ i x => ∃ y, x = Container.M.corec (automaton f) ⟨i, y⟩) ≤ WellFormed :=
by
  simp only [WellFormed, PWellFormed]
  rw [pgfp.coinduction]
  intro i x ⟨y, h₀⟩
  cases h₀
  constructor
  . simp only [Container.M.destruct_corec, Container.Map, automaton]
  . intro z
    apply Or.inl
    exists (f _ y).snd _

#check 42

def M.corec (f:(i:I) → α i → Obj C α i) {i:I} (x₀:α i) : M C i where
  val := Container.M.corec (corec.automaton f) ⟨i, x₀⟩
  property := by
    apply corec.automaton.wf f
    exists x₀


#check Sigma.snd_equals

def M.unfolded_eq {i:I} : ∀ (x y:Obj C (M C) i),
  Map (λ i x => x.val) x = Map (λ i x => x.val) y → x = y
| ⟨x, fx⟩, ⟨y, fy⟩ => by
  intro h
  simp only [Map] at h
  have h' := congrArg (λ x => x.fst) h
  cases h'
  have h' := congrFun (Sigma.snd_equals _ _ _ h)
  apply Sigma.snd_equals
  apply Sigma.snd_equals
  simp only [Sigma.mk.inj_iff, true_and, heq_eq_eq]
  funext x
  have h' := h' x
  apply Subtype.eq
  assumption

#check Container.M.destruct_corec

def Sigma.mk_dest {α:Type _} {β: α → Type _} :
  ∀ x:(Σ a:α, β a), ⟨x.fst, x.snd⟩ = x := by
  intro ⟨a, b⟩
  rfl

#check Sigma.snd_equals

#check Sigma.mk.inj_iff

def M.destruct_corec (f:(i:I) → α i → Obj C α i) {i:I} (x₀:α i) :
  destruct (corec f x₀) = Map (λ i => @corec I C α f i) (f i x₀) := by
  simp only [cast_eq, destruct, corec, Map]
  have h := Container.M.destruct_corec (corec.automaton f) ⟨i, x₀⟩
  let from_x₀ := Container.M.destruct (Container.M.corec (corec.automaton f) ⟨i, x₀⟩)
  conv at h =>
    rhs
    rhs
    simp only [corec.automaton]
  cases h': f i x₀ with
  | mk a b =>
    rw [h'] at h
    simp only
    have h₁ : from_x₀.fst.snd = a := by
      have h := congrArg (λ x => x.fst) h
      have h : ⟨from_x₀.fst.fst, from_x₀.fst.snd⟩ = Sigma.mk i a := by
        rw [Sigma.mk_dest from_x₀.fst]
        exact h
      rw [Sigma.mk.inj_iff] at h
      apply eq_of_heq
      exact h.right

    induction h₁

    let from_x₀_snd := λ y => Container.M.corec (corec.automaton f) ⟨_, b y⟩
    have h₁: from_x₀.snd = from_x₀_snd := by
      simp only [Container.Map] at h
      have h : from_x₀ = Sigma.mk from_x₀.fst from_x₀_snd  := h
      have : from_x₀ = Sigma.mk from_x₀.fst from_x₀.snd := by rfl
      conv at h =>
        lhs
        rw [this]
        rfl
      exact Sigma.snd_equals _ _ _ h

    rw [Sigma.mk.inj_iff]
    constructor
    . rfl
    . simp only [heq_eq_eq]
      funext y
      simp only [Subtype.mk.injEq]
      conv =>
        lhs
        rw [h₁]
        rfl


end IContainer

#check IContainer
#check IContainer.Obj
#check IContainer.Map
#check IContainer.M
#check IContainer.M.destruct
#check IContainer.M.corec
#check IContainer.M.destruct_corec
#check IContainer.M.bisim

