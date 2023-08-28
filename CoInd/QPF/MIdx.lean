import CoInd.Container
import CoInd.MIdx
import CoInd.QPF.Basics


variable {I: Type u₁}
variable (F: (I → Type u₁) → I → Type u₁)
variable [inst:IQPF F]

def IQPF.M.map_quot
  (r: (i:I) → IContainer.M inst.C i → IContainer.M inst.C i → Prop)
  {i:I} (x: IContainer.M inst.C i) : F (λ i => Quot (r i)) i := inst.abs <| IContainer.Map (λ i => Quot.mk (r i)) (IContainer.M.destruct x)

#check IQPF.M.map_quot

#check Quot
#check Quot.mk
#check Quot.lift
#check Quot.ind
#check Quot.sound

def IQPF.M.precongr : ((i:I) → IContainer.M inst.C i → IContainer.M inst.C i → Prop) →o ((i:I) → IContainer.M inst.C i → IContainer.M inst.C i → Prop) where
  toFun r i x y := map_quot F r x = map_quot F r y

  monotone' := by
    intro p q h₀ i x y h₁
    simp only [map_quot] at *
    simp only [IContainer.Map] at *
    generalize IContainer.M.destruct x = x at *
    generalize IContainer.M.destruct y = y at *
    cases x with
    | mk nx kx =>
      cases y with
      | mk ny ky =>
        simp only at *
        have h₂: ∀ (i:I) (a b : IContainer.M (C F) i), p i a b → Quot.mk (q i) a = Quot.mk (q i) b := by
          intro i a b h₂
          apply Quot.sound
          apply h₀
          exact h₂
        let f : (i: I) → Quot (p i) → Quot (q i) := λ i x =>
          Quot.lift (Quot.mk (q i)) (h₂ i) x
        have h₄ := congrArg (inst.imap f) h₁
        rw [←inst.abs_imap, ←inst.abs_imap] at h₄
        assumption

abbrev IQPF.M.pcongr p := pgfp (precongr F) p
abbrev IQPF.M.congr := pcongr F ⊥

#check pgfp.coinduction
#check le_trans

open IContainer in
theorem IQPF.M.congr.coinduction (p:(i:I) → M inst.C i → M inst.C i → Prop) :
  (∀ i x y, p i x y → precongr F p i x y) → ∀ i x y, p i x y → congr F i x y := by
  intro h₀ i x y h₁
  simp only [congr, pcongr]
  have := (pgfp.coinduction (precongr F) p).2
  apply this
  have : p ≤ p ⊔ pgfp (precongr F) p := by
    simp
  have := (precongr F).2 this
  apply le_trans _ this
  apply h₀
  assumption

def IQPF.M i := Quot (IQPF.M.congr F i)

def IQPF.M.destruct.f {i:I} (x:IContainer.M (C F) i) : F (M F) i :=
  inst.imap (λ _ x => Quot.mk _ x) <| inst.abs <| IContainer.M.destruct x

open IContainer in
def IQPF.M.destruct.congr {i:I} :
  ∀ a b:IContainer.M (C F) i, congr F i a b → destruct.f F a = destruct.f F b := by
  intro x y h₁
  simp only [destruct.f, ←inst.abs_imap, Map]
  cases h₂: M.destruct x with
  | mk nx kx =>
    cases h₃: M.destruct y with
    | mk ny ky =>
      simp only
      have h₁ : map_quot F (IQPF.M.congr F) x = map_quot F (IQPF.M.congr F) y := by
        simp only [IQPF.M.congr, pcongr] at h₁
        rw [←pgfp.unfold, CompleteLattice.bot_sup] at h₁
        exact h₁
      simp only [map_quot, Map, h₂, h₃] at h₁
      exact h₁

def IQPF.M.destruct {i:I} : IQPF.M F i → F (IQPF.M F) i :=
  Quot.lift (destruct.f F) (destruct.congr F)

open IContainer in
def IQPF.M.corec {α: I → Type u₁} (f:(i:I) → α i → F α i) {i:I} (x₀:α i) : IQPF.M F i :=
  Quot.mk _ (IContainer.M.corec (λ i x => inst.repr <| f i x) x₀)

theorem IQPF.M.destruct_corec {α: I → Type u₁} (f:(i:I) → α i → F α i) {i:I} (x₀:α i) :
  destruct F (corec F f x₀) = inst.imap (λ i x => corec F f x) (f i x₀) := by
  simp only [IQPF.M.destruct, IQPF.M.corec, destruct.f, IContainer.M.destruct_corec, inst.abs_imap, inst.abs_repr]
  rw [←inst.abs_repr (f i x₀)]
  cases repr (f i x₀) with
  | mk n k =>
    simp only [←inst.abs_imap, IContainer.Map]

def IQPF.M.liftp {α: I → Type u₁}
  (p: (i:I) → α i → Prop) (i:I) (x:F α i) : Prop :=
    ∃ z: F (λ i => {x:α i // p i x}) i,
      inst.imap (λ _ x => x.1) z = x

def IQPF.M.liftr {α β: I → Type u₁}
  (r: (i:I) → α i → β i → Prop) : (i:I) → F α i → F β i → Prop :=
  λ i x y => ∃ z: F (λ i => {p:α i × β i // r i p.1 p.2}) i,
    inst.imap (λ _ x => x.1.1) z = x ∧ inst.imap (λ _ x => x.1.2) z = y

#check IQPF.M.congr.coinduction F
#check pgfp.unfold

theorem IQPF.M.imap_spec {α β γ:I → Type u₁} (f: (i:I) → β i → γ i) (g:(i:I) → α i → β i) (x: F α i) :
  inst.imap (λ i => f i ∘ g i) x = inst.imap f (inst.imap g x) := by
  conv =>
    congr
    <;> rw [←inst.abs_repr x]
  cases repr x
  simp [←inst.abs_imap, IContainer.Map]

theorem IContainer.Map_spec {α β γ:I → Type u₁} (f: (i:I) → β i → γ i) (g:(i:I) → α i → β i) (x: inst.C.Obj α i) :
  IContainer.Map (λ i => f i ∘ g i) x = IContainer.Map f (IContainer.Map g x) := by
  cases x
  simp [IContainer.Map]

theorem IQPF.M.bisim_lemma (r: (i:I) → M F i → M F i → Prop)
  (h₀: ∀ i x, r i x x)
  (h₁: ∀ i x y, r i x y →
    inst.imap (λ i => Quot.mk (r i)) (destruct F x) = inst.imap (λ i => Quot.mk (r i)) (destruct F y)) :
  ∀ i x y, r i x y → x = y := by
  intro i x
  apply Quot.inductionOn (motive := _) x
  clear x
  intro x y
  apply Quot.inductionOn (motive := _) y
  clear y
  intro y h₂
  apply Quot.sound
  let r' i x y := r i (Quot.mk _ x) (Quot.mk _ y)
  apply congr.coinduction F r'
  . clear h₂
    intro i x y h₂
    simp only [precongr, map_quot]
    have h₂ := h₁ i _ _ h₂
    simp only [destruct, destruct.f] at h₂
    generalize IContainer.M.destruct x = x at *
    generalize IContainer.M.destruct y = y at *
    cases x with | mk nx kx =>
    cases y with | mk ny ky =>
    --simp only [Map] at *
    let f i : Quot (r i) → Quot (r' i) :=
      by
        apply Quot.lift (Quot.lift (Quot.mk (r' _)) _) _
        . intro a b h₃
          apply Quot.sound
          simp only
          rw [Quot.sound h₃]
          apply h₀
        . intro x; apply Quot.inductionOn (motive := _) x; clear x
          intro x y; apply Quot.inductionOn (motive := _) y; clear y
          intro y h
          apply Quot.sound
          apply h
    have : ∀ i, f i ∘ Quot.mk (r _) ∘ Quot.mk (congr F _) = Quot.mk (r' _) := by intro i; rfl
    conv =>
      congr
      . rhs
        lhs
        intro i
        rw [←this]
        rfl
      . rhs
        lhs
        intro i
        rw [←this]
    rw [IContainer.Map_spec F, IContainer.Map_spec F, IContainer.Map_spec F, IContainer.Map_spec F]
    rw [inst.abs_imap, inst.abs_imap, inst.abs_imap, inst.abs_imap, inst.abs_imap, inst.abs_imap, h₂]
  . apply h₂

theorem IQPF.M.bisim (r:(i:I) → M F i → M F i → Prop)
  (h₀: ∀ i x y, r i x y → liftr F r i (destruct F x) (destruct F y)) :
  ∀ {i} x y, r i x y → x = y := by
  intro i x y h₁
  apply bisim_lemma F (λ i x y => x = y ∨ r i x y)
  . intro _ _
    left
    rfl
  . intro i x y h₂
    cases h₂
    case inl h₂ =>
      rw [h₂]
    case inr h₂ =>
      have ⟨z, h₃⟩ := h₀ _ _ _ h₂
      clear h₂
      rw [←h₃.1, ←h₃.2]
      clear h₃
      rw [←imap_spec, ←imap_spec]
      conv =>
        congr <;> rw [←abs_repr z]
      rw [←abs_imap]
      rw [←abs_imap]
      cases repr z with | mk nz kz =>
      simp only [IContainer.Map, Function.comp]
      apply congrArg abs
      rw [Sigma.mk.inj_iff]
      simp only [true_and, heq_eq_eq]
      funext a
      apply Quot.sound
      right
      apply (kz a).2
  . right; assumption

#print IQPF
#check IQPF.M
#check IQPF.M.destruct
#check IQPF.M.corec
#check IQPF.M.destruct_corec
#check IQPF.M.bisim


