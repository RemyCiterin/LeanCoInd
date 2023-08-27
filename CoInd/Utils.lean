import CoInd.M
import CoInd.Indexed

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

namespace IContainer

class IFunctor {I:Type u₁} (F: (I → Type u₁) → I → Type u₂) where
  imap : {α β: I → Type u₁} → (f:(i:I) → α i → β i) → {i:I} → F α i → F β i

class IQPF {I:Type u₁} (F: (I → Type u₁) → I → Type u₁) extends IFunctor F where
  C: IContainer.{u₁} I
  abs: ∀ {α:I → Type u₁} {i:I}, C.Obj α i → F α i
  repr: ∀ {α: I → Type u₁} {i:I}, F α i → C.Obj α i
  abs_repr: ∀ {α: I → Type u₁} {i:I} (x:F α i), abs (repr x) = x
  abs_imap: ∀ {α β:I → Type u₁} (f:(i:I) → α i → β i) (p:C.Obj α i), abs (C.Map f p) = imap f (abs p)


variable {I: Type u₁}
variable (F: (I → Type u₁) → I → Type u₁)
variable [inst:IQPF F]

def IQPF.map_quot
  (r: (i:I) → M inst.C i → M inst.C i → Prop)
  {i:I} (x: M inst.C i) : F (λ i => Quot (r i)) i := inst.abs <| Map (λ i => Quot.mk (r i)) (M.destruct x)

#check IQPF.map_quot

#check Quot
#check Quot.mk
#check Quot.lift
#check Quot.ind
#check Quot.sound

def IQPF.precongr : ((i:I) → M inst.C i → M inst.C i → Prop) →o ((i:I) → M inst.C i → M inst.C i → Prop) where
  toFun r i x y := map_quot F r x = map_quot F r y

  monotone' := by
    intro p q h₀ i x y h₁
    simp only [map_quot] at *
    simp only [Map] at *
    generalize M.destruct x = x at *
    generalize M.destruct y = y at *
    cases x with
    | mk nx kx =>
      cases y with
      | mk ny ky =>
        simp only at *
        have h₂: ∀ (i:I) (a b : M (C F) i), p i a b → Quot.mk (q i) a = Quot.mk (q i) b := by
          intro i a b h₂
          apply Quot.sound
          apply h₀
          exact h₂
        let f : (i: I) → Quot (p i) → Quot (q i) := λ i x =>
          Quot.lift (Quot.mk (q i)) (h₂ i) x
        have h₄ := congrArg (inst.imap f) h₁
        rw [←inst.abs_imap, ←inst.abs_imap] at h₄
        assumption

abbrev IQPF.pcongr p := pgfp (precongr F) p
abbrev IQPF.congr := pcongr F ⊥

#check pgfp.coinduction
#check pgfp.accumulate (IQPF.precongr F)
#check (pgfp (IQPF.precongr F)).2
#check (IQPF.precongr F).2
#check le_trans

theorem IQPF.congr.coinduction (p:(i:I) → M inst.C i → M inst.C i → Prop) :
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

def IQPF.Mtype i := Quot (congr F i)

def IQPF.destruct.f {i:I} (x:M (C F) i) : F (Mtype F) i :=
  inst.imap (λ _ x => Quot.mk _ x) <| inst.abs <| M.destruct x

def IQPF.destruct.congr {i:I} :
  ∀ a b:M (C F) i, congr F i a b → destruct.f F a = destruct.f F b := by
  intro x y h₁
  simp only [destruct.f, ←inst.abs_imap, Map]
  cases h₂: M.destruct x with
  | mk nx kx =>
    cases h₃: M.destruct y with
    | mk ny ky =>
      simp only
      have h₁ : map_quot F (IQPF.congr F) x = map_quot F (IQPF.congr F) y := by
        simp only [IQPF.congr, pcongr] at h₁
        rw [←pgfp.unfold, CompleteLattice.bot_sup] at h₁
        exact h₁
      simp only [map_quot, Map, h₂, h₃] at h₁
      exact h₁

def IQPF.destruct {i:I} : IQPF.Mtype F i → F (IQPF.Mtype F) i :=
  Quot.lift (destruct.f F) (destruct.congr F)

def IQPF.corec {α: I → Type u₁} (f:(i:I) → α i → F α i) {i:I} (x₀:α i) : Mtype F i :=
  Quot.mk _ (M.corec (λ i x => inst.repr <| f i x) x₀)

theorem IQPF.destruct_corec {α: I → Type u₁} (f:(i:I) → α i → F α i) {i:I} (x₀:α i) :
  destruct F (corec F f x₀) = inst.imap (λ i x => corec F f x) (f i x₀) := by
  simp only [destruct, corec, destruct.f, M.destruct_corec, inst.abs_imap, inst.abs_repr]
  rw [←inst.abs_repr (f i x₀)]
  cases repr (f i x₀) with
  | mk n k =>
    simp only [←inst.abs_imap, Map]

def IQPF.liftp {α: I → Type u₁}
  (p: (i:I) → α i → Prop) (i:I) (x:F α i) : Prop :=
    ∃ z: F (λ i => {x:α i // p i x}) i,
      inst.imap (λ _ x => x.1) z = x

def IQPF.liftr {α β: I → Type u₁}
  (r: (i:I) → α i → β i → Prop) : (i:I) → F α i → F β i → Prop :=
  λ i x y => ∃ z: F (λ i => {p:α i × β i // r i p.1 p.2}) i,
    inst.imap (λ _ x => x.1.1) z = x ∧ inst.imap (λ _ x => x.1.2) z = y

#check IQPF.congr.coinduction F
#check pgfp.unfold

theorem IQPF.imap_spec {α β γ:I → Type u₁} (f: (i:I) → β i → γ i) (g:(i:I) → α i → β i) (x: F α i) :
  inst.imap (λ i => f i ∘ g i) x = inst.imap f (inst.imap g x) := by
  conv =>
    congr
    <;> rw [←inst.abs_repr x]
  cases repr x
  simp [←inst.abs_imap, Map]

theorem Map_spec {α β γ:I → Type u₁} (f: (i:I) → β i → γ i) (g:(i:I) → α i → β i) (x: inst.C.Obj α i) :
  Map (λ i => f i ∘ g i) x = Map f (Map g x) := by
  cases x
  simp [Map]

theorem IQPF.bisim_lemma (r: (i:I) → Mtype F i → Mtype F i → Prop)
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
    generalize M.destruct x = x at *
    generalize M.destruct y = y at *
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
    rw [Map_spec F, Map_spec F, Map_spec F, Map_spec F]
    rw [inst.abs_imap, inst.abs_imap, inst.abs_imap, inst.abs_imap, inst.abs_imap, inst.abs_imap, h₂]
  . apply h₂

theorem IQPF.bisim (r:(i:I) → Mtype F i → Mtype F i → Prop)
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
      simp only [Map, Function.comp]
      apply congrArg abs
      --apply Sigma.snd_equals
      rw [Sigma.mk.inj_iff]
      simp only [true_and, heq_eq_eq]
      funext a
      apply Quot.sound
      right
      apply (kz a).2
  . right; assumption

#print IQPF
#check IQPF.Mtype
#check IQPF.destruct
#check IQPF.corec
#check IQPF.destruct_corec
#check IQPF.bisim

end IContainer
