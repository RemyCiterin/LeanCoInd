import CoInd.M
import CoInd.Paco
import CoInd.QPF.Basics


variable {F: Type u₁ → Type u₁}
variable [inst:QPF F]

open Container in
def QPF.M.map_quot (F:Type u₁ → Type u₁) [inst:QPF F]
  (r: M inst.C → M inst.C → Prop)
  (x: M inst.C) : F (Quot r) := inst.abs <| Map (Quot.mk r) (M.destruct x)

#check QPF.M.map_quot

#check Quot
#check Quot.mk
#check Quot.lift
#check Quot.ind
#check Quot.sound

open Container in
def QPF.M.precongr (F:Type u₁ → Type u₁) [inst:QPF F]
  : (M inst.C → M inst.C → Prop) →o (M inst.C → M inst.C → Prop) where
  toFun r x y := map_quot F r x = map_quot F r y

  monotone' := by
    intro p q h₀ x y h₁
    simp only [map_quot] at *
    simp only [Map] at *
    generalize M.destruct x = x at *
    generalize M.destruct y = y at *
    cases x with
    | mk nx kx =>
      cases y with
      | mk ny ky =>
        simp only at *
        have h₂: ∀ (a b : M inst.C), p a b → Quot.mk q a = Quot.mk q b := by
          intro a b h₂
          apply Quot.sound
          apply h₀
          exact h₂
        let f : Quot (p) → Quot q := λ x =>
          Quot.lift (Quot.mk q) (h₂) x
        have h₄ := congrArg (inst.map f) h₁
        rw [←inst.abs_map, ←inst.abs_map] at h₄
        assumption

abbrev QPF.M.pcongr (F:Type u₁ → Type u₁) [inst:QPF F] p := pgfp (precongr F) p
abbrev QPF.M.congr (F:Type u₁ → Type u₁) [inst:QPF F] := pcongr F ⊥

#check pgfp.coinduction
#check le_trans

open Container in
theorem QPF.M.congr.coinduction (F:Type u₁ → Type u₁) [inst:QPF F] (p:M inst.C → M inst.C → Prop) :
  (∀ x y, p x y → precongr F p x y) → ∀ x y, p x y → congr F x y := by
  intro h₀ x y h₁
  simp only [congr, pcongr]
  have := (pgfp.coinduction (precongr F) p).2
  apply this
  have : p ≤ p ⊔ pgfp (precongr F) p := by
    simp
  have := (precongr F).2 this
  apply le_trans _ this
  apply h₀
  assumption

def QPF.M (F:Type u₁ → Type u₁) [inst:QPF F] := Quot (QPF.M.congr F)


def QPF.M.destruct.f (x:Container.M (C F)) : F (M F) :=
  inst.map (λ x => Quot.mk _ x) <| inst.abs <| Container.M.destruct x

def QPF.M.destruct.congr :
  ∀ a b:Container.M (C F), congr F a b → destruct.f a = destruct.f b := by
  intro x y h₁
  simp only [destruct.f, ←inst.abs_map, Container.Map]
  cases h₂: Container.M.destruct x with
  | mk nx kx =>
    cases h₃: Container.M.destruct y with
    | mk ny ky =>
      simp only
      have h₁ : map_quot F (QPF.M.congr F) x = map_quot F (QPF.M.congr F) y := by
        simp only [QPF.M.congr, pcongr] at h₁
        rw [←pgfp.unfold, CompleteLattice.bot_sup] at h₁
        exact h₁
      simp only [map_quot, Container.Map] at h₁
      rw [h₂, h₃] at h₁
      exact h₁

def QPF.M.destruct : QPF.M F → F (QPF.M F) :=
  Quot.lift (destruct.f) (destruct.congr)

def QPF.M.corec {α: Type u₁} (f:α → F α) (x₀:α) : M F :=
  Quot.mk _ (Container.M.corec (λ x => inst.repr <| f x) x₀)

theorem QPF.M.destruct_corec {α:Type u₁} (f:α → F α) (x₀:α) :
  destruct (corec f x₀) = inst.map (λ x => corec f x) (f x₀) := by
  simp only [destruct, corec, destruct.f, Container.M.destruct_corec, inst.abs_map, inst.abs_repr]
  rw [←inst.abs_repr (f x₀)]
  cases repr (f x₀) with
  | mk n k =>
    simp only [←inst.abs_map, Container.Map]
    rfl

def QPF.M.liftp (F:Type u₁ → Type u₁) [inst:Functor F] {α:Type u₁}
  (p: α → Prop) (x:F α) : Prop :=
    ∃ z: F {x:α // p x},
      inst.map (λ x => x.1) z = x

def QPF.M.liftr (F:Type u₁ → Type u₁) [inst:Functor F] {α β:Type u₁}
  (r: α → β → Prop) : F α → F β → Prop :=
  λ x y => ∃ z: F {p:α × β // r p.1 p.2},
    inst.map (λ x => x.1.1) z = x ∧ inst.map (λ x => x.1.2) z = y

#check pgfp.unfold

theorem QPF.M.map_comp {α β γ:Type u₁} (f: β → γ) (g:α → β) (x: F α) :
  inst.map (f ∘ g) x = inst.map f (inst.map g x) := by
  conv =>
    congr
    <;> rw [←inst.abs_repr x]
  cases repr x
  simp [←inst.abs_map, Container.Map]
  rfl

open Container in
theorem Container.Map_spec {α β γ:Type u₁} (f: β → γ) (g:α → β) (x: inst.C.Obj α) :
  Map (f ∘ g) x = Map f (Map g x) := by
  cases x
  simp [Map]
  rfl

theorem QPF.M.bisim_lemma (r: M F → M F → Prop)
  (h₀: ∀ x, r x x)
  (h₁: ∀ x y, r x y →
    inst.map (Quot.mk r) (destruct x) = inst.map (Quot.mk r) (destruct y)) :
  ∀ x y, r x y → x = y := by
  intro x
  apply Quot.inductionOn (motive := _) x
  clear x
  intro x y
  apply Quot.inductionOn (motive := _) y
  clear y
  intro y h₂
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  apply congr.coinduction F r'
  . clear h₂
    intro x y h₂
    simp only [precongr, map_quot]
    have h₂ := h₁ _ _ h₂
    simp only [destruct, destruct.f] at h₂
    generalize Container.M.destruct x = x at *
    generalize Container.M.destruct y = y at *
    cases x with | mk nx kx =>
    cases y with | mk ny ky =>
    --simp only [Map] at *
    let f : Quot r → Quot r' :=
      by
        apply Quot.lift (Quot.lift (Quot.mk r') _) _
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
    have : f ∘ Quot.mk r ∘ Quot.mk (congr F) = Quot.mk r' := rfl
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
    rw [Container.Map_spec, Container.Map_spec, Container.Map_spec, Container.Map_spec]
    rw [inst.abs_map, inst.abs_map, inst.abs_map, inst.abs_map, inst.abs_map, inst.abs_map, h₂]
  . apply h₂

#check Sigma.mk.inj_iff

theorem QPF.M.bisim (r:M F → M F → Prop)
  (h₀: ∀ x y, r x y → liftr F r (destruct x) (destruct y)) :
  ∀ x y, r x y → x = y := by
  intro x y h₁
  apply bisim_lemma (λ x y => x = y ∨ r x y)
  . intro _
    left
    rfl
  . intro x y h₂
    cases h₂
    case inl h₂ =>
      rw [h₂]
    case inr h₂ =>
      have ⟨z, h₃⟩ := h₀ _ _ h₂
      clear h₂
      rw [←h₃.1, ←h₃.2]
      clear h₃
      rw [←map_comp, ←map_comp]
      conv =>
        congr <;> rw [←abs_repr z]
      rw [←abs_map]
      rw [←abs_map]
      cases repr z with | mk nz kz =>
      simp only [Container.Map, Function.comp]
      apply congrArg abs
      rw [Container.Obj.snd_equals_iff]
      funext a
      apply Quot.sound
      right
      apply (kz a).2
  . right; assumption

#print QPF
#check QPF.M
#check QPF.M.destruct
#check QPF.M.corec
#check QPF.M.destruct_corec
#check QPF.M.bisim

