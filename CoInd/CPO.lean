import CoInd.Paco
import Mathlib.Order.FixedPoints
import Mathlib.Tactic.Monotonicity.Basic
import CoInd.Container


#check Bot

class ωCPO (D: Type u) extends Preorder D, Bot D where
  bot_le : ∀ x:D, ⊥ ≤ x
  lub : (Nat →o D) → D
  le_lub : ∀ {f: Nat →o D} {n: Nat}, f n ≤ lub f
  lub_le : ∀ {f: Nat →o D} {x: D}, (∀ n, f n ≤ x) → lub f ≤ x


namespace ωCPO
open ωCPO

variable {D₁: Type u₁} [inst₁: ωCPO D₁]
variable {D₂: Type u₂} [inst₂: ωCPO D₂]
variable {D₃: Type u₃} [inst₃: ωCPO D₃]
variable {D₄: Type u₄} [inst₄: ωCPO D₄]

@[mono]
theorem le_lub' (f: ℕ →o D₁) (n: ℕ) : f n ≤ lub f :=
  le_lub

theorem lub_le' (f: ℕ →o D₁) (x: D₁) : (∀ n, f n ≤ x) → lub f ≤ x :=
  lub_le

@[mono]
theorem compose_lub (F : D₁ →o D₂) (f : Nat →o D₁) :
  lub (F.comp f) ≤ F (lub f) := by
  apply lub_le
  intro n
  apply F.monotone'
  apply le_lub

def continuous {D₁: Type u₁} {D₂: Type u₂} [ωCPO D₁] [ωCPO D₂] (F: D₁ →o D₂) :=
  ∀ f: ℕ →o D₁, F (lub f ) ≤ lub (F.comp f)

structure Continuous (D₁: Type u₁) (D₂: Type u₂) [inst₁: ωCPO D₁] [inst₂: ωCPO D₂] extends D₁ →o D₂ where
  continuous' : continuous toOrderHom


infixr:25 " →c " => Continuous

instance : Coe (D₁ →c D₂) (D₁ →o D₂) where
  coe := Continuous.toOrderHom

@[coe]
def toFun (F: D₁ →c D₂) : D₁ → D₂ :=
  F.toOrderHom

instance instFunLike : FunLike (D₁ →c D₂) D₁ (λ _ => D₂) where
  coe := toFun
  coe_injective'  := by
    intro ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h
    simp only [toFun, OrderHom.toFun] at h
    congr

@[mono]
def Continuous.apply  {D₁: Type u₁} {D₂: Type u₂} [ωCPO D₁] [ωCPO D₂] (F: D₁ →c D₂) :
  ∀ f: ℕ →o D₁, F (lub f) ≤ lub (F.toOrderHom.comp f) :=
  F.continuous'

#check OrderHom.mono
@[mono] def Continuous.mono (f: D₁ →c D₂) (x y: D₁) :
  x ≤ y → f x ≤ f y := λ h => OrderHom.mono f.toOrderHom h

#check OrderHom.curry
#check OrderHom.fst
#check OrderHom.snd

def Continuous.comp (f: D₂ →c D₃) (g: D₁ →c D₂) : D₁ →c D₃ where
  toOrderHom := f.toOrderHom.comp g
  continuous' := λ h =>
    (f.toOrderHom.monotone' (g.continuous' h)).trans (f.continuous' _)

def Continuous.id (D: Type u) [ωCPO D] : D →c D where
  toOrderHom := OrderHom.id
  continuous' := by
    intro f
    apply le_rfl

@[simp] def Continuous.comp_id (f: D₁ →c D₂) : f.comp (id _) = f := Eq.refl _
@[simp] def Continuous.id_comp (f: D₁ →c D₂) : (id _).comp f = f := Eq.refl _

@[simp] def Continuous.comp_assoc (f: D₃ →c D₄) (g: D₂ →c D₃) (h: D₁ →c D₂) :
  (f.comp g).comp h = f.comp (g.comp h) := Eq.refl _

@[mono]
def comp.monotone_left {D₁: Type u₁} {D₂: Type u₂} [Preorder D₁] [Preorder D₂]
  (f g: D₂ →o D₃) (h: D₁ →o D₂) : f ≤ g → f.comp h ≤ g.comp h :=
  λ h₁ x => h₁ (h x)

@[mono]
def comp.monotone_right {D₁: Type u₁} {D₂: Type u₂} [Preorder D₁] [Preorder D₂]
  (f: D₂ →o D₃) (g h: D₁ →o D₂) : g ≤ h → f.comp g ≤ f.comp h :=
  λ h₁ x => f.monotone' (h₁ x)


instance {A: Type u₀} : ωCPO (A → D₁) where
  bot_le (f: A → D₁) x := inst₁.bot_le (f x)

  lub (f: Nat →o (A → D₁)) := λ (x:A) => lub ⟨λ n => f n x, λ n m h₁ => f.monotone' h₁ x⟩

  lub_le := by
    intro f F h₁ x
    apply lub_le
    intro n
    apply h₁ n

  le_lub := by
    intro f n x
    apply LE.le.trans _ (@le_lub _ _ _ n)
    apply le_refl

@[mono]
def lub.monotone (f g: Nat →o D₁) : f ≤ g → lub f ≤ lub g := by
  intro h
  apply lub_le
  intro n
  apply (h n).trans
  mono

instance {A: Type u₀} [Preorder A] : ωCPO (A →o D₁) where
  bot := {
    toFun := @Bot.bot (A → D₁) _,
    monotone' := by
      intro _ _ _
      simp only [Pi.bot_apply, le_refl]
  }

  bot_le f x := @ωCPO.bot_le _ _ _

  lub f := {
    toFun := @ωCPO.lub (A → D₁) _ ⟨λ n => f n, λ a b h₁ => f.monotone' h₁⟩,
    monotone' := by
      intro a b h₁
      apply @ωCPO.lub_le
      intro n
      simp only
      apply ((f n).monotone' h₁).trans _
      apply LE.le.trans _ (@le_lub _ _ _ n)
      apply le_refl
  }

  le_lub :=
    λ {f n} x => @le_lub (A → D₁) _ ⟨λ n => f n, λ a b h₁ => f.monotone' h₁⟩ n x

  lub_le := λ {f} F h₁ x =>
    @lub_le (A → D₁) _ ⟨λ n => f n, λ a b h₁ => f.monotone' h₁⟩ F h₁ x

#check bot_le

#print ωCPO
#print toBot
#print Bot
#print OrderBot


instance {A: Type u₀} [ωCPO A] : Preorder (A →c D₁) where
  le f g := f.toOrderHom ≤ g.toOrderHom

  le_refl a := @le_refl (A →o D₁) _ a

  le_trans a b c := @le_trans (A →o D₁) _ a b c


instance {A: Type u₀} [ωCPO A] : ωCPO (A →c D₁) where
  bot := {
    toOrderHom := @Bot.bot (A →o D₁) _,
    continuous' := by
      intro f
      conv =>
        lhs
        simp only [Bot.bot]
        rfl
      exact @bot_le _ _ <| lub (OrderHom.comp ⊥ f)
  }

  bot_le f x := bot_le (toFun f x)

  lub (f: Nat →o (A →c D₁)) : A →c D₁ := {
    toOrderHom := @lub (A →o D₁) _ ⟨λ n => f n, λ x b h => f.monotone' h⟩,
    continuous' := by
      intro F
      apply lub_le
      intro n
      apply ((f n).continuous' _).trans
      simp only
      apply lub.monotone
      apply comp.monotone_left _ _
      apply LE.le.trans _ (@le_lub _ _ _ n)
      apply le_refl
  }

  le_lub {f n} x := by
    apply LE.le.trans _ (@le_lub _ _ _ n)
    apply le_refl

  lub_le {f F h₁} x := by
    apply lub_le
    intro n
    apply h₁ n


instance : ωCPO (D₁ × D₂) where
  bot_le
  | (x, y) => by
    constructor
    . apply bot_le
    . apply bot_le

  lub (f: Nat →o D₁ × D₂) := (inst₁.lub (OrderHom.fst.comp f), inst₂.lub (OrderHom.snd.comp f))

  le_lub := by
    intro f n
    have : f n = (OrderHom.fst.comp f n, OrderHom.snd.comp f n) := Eq.refl _
    rw [this]
    constructor
    . apply @le_lub _ _ (OrderHom.fst.comp f)
    . apply @le_lub _ _ (OrderHom.snd.comp f)

  lub_le := by
    intro f ⟨x, y⟩ h₁
    constructor
    . apply lub_le
      intro n
      apply (h₁ n).1
    . apply lub_le
      intro n
      apply (h₁ n).2

def fst : (D₁ × D₂) →c D₁ where
  toOrderHom := OrderHom.fst
  continuous' := by
    intro f
    simp only [OrderHom.fst_coe, lub, le_refl]

def snd : (D₁ × D₂) →c D₂ where
  toOrderHom := OrderHom.snd
  continuous' := by
    intro f
    simp only [OrderHom.snd_coe, lub, le_refl]

def const : D₂ →c D₁ →c D₂ where
  toFun x :=
    { toFun := λ _ => x
    , monotone' := λ _ _ _ => le_refl x
    , continuous' := λ f => @le_lub _ _ (OrderHom.comp ⟨λ _ => x, λ _ _ _ => le_refl x⟩ f) 0}
  monotone' := by
    intro a b h x
    simp only
    exact h
  continuous' := by
    intro f x
    simp only [OrderHom.comp, Function.comp, lub, le_refl]

#check OrderHom.prod
#check le_lub'
def prod : D₁ →c (D₂ →c (D₁ × D₂)) where
  toFun x := {
      toFun := λ y => (x, y),
      monotone' := by
        intro x y h₁
        simp only [Prod.mk_le_mk, le_refl, true_and]
        exact h₁,
      continuous' := by
        intro f
        simp only [ωCPO.lub, Prod.mk_le_mk]
        constructor
        . exact le_lub' (OrderHom.const ℕ x) 0
        . exact le_refl (lub f)
    }
  monotone' := by
    intro a b h x
    simp only [Prod.mk_le_mk, le_refl, and_true]
    exact h
  continuous' := by
    intro f x
    simp only
      [OrderHom.comp_coe, Function.comp_apply, Prod.mk_le_mk,
      lub, OrderHom.comp, OrderHom.fst, OrderHom.snd, Function.comp]
    constructor
    . exact le_refl (lub f)
    . exact le_lub' (OrderHom.const ℕ x) 0

--def curry : (D₁ × D₂ →c D₃) →c D₁ →c D₂ →c D₃ where
--  toFun fromPair := fromPair.comp prod

instance {I: Type u} {D: I → Type v} [inst:∀ i:I, ωCPO (D i)] : ωCPO (∀ i:I, D i) where
  bot_le x := by
    intro i
    apply (inst i).bot_le

  lub f i := (inst i).lub ⟨λ n => f n i, λ a b h => f.monotone' h _⟩

  le_lub {f n} i :=
    (inst i).le_lub' ⟨λ n => f n i, λ a b h => f.monotone' h _⟩ n

  lub_le {f x} h i := by
    apply (inst i).lub_le' ⟨λ n => f n i, λ a b h => f.monotone' h _⟩ _
    intro n
    apply h

def proj {I: Type u} {D: I → Type v} [inst:∀ i:I, ωCPO (D i)] (i:I) : (∀ i:I, D i) →c D i where
  toFun arrow := arrow i
  monotone' := by
    intro a b h
    apply h
  continuous' := by
    intro f
    apply le_refl

@[simp] def proj_apply {I: Type u} {D: I → Type v} [∀ i:I, ωCPO (D i)] (i:I) (p: ∀ i, D i) :
  proj i p = p i := Eq.refl _

def map  {I: Type u} {D₁: I → Type v} {D₂: I → Type w}
  [inst₁:∀ i:I, ωCPO (D₁ i)] [inst₂: ∀ i, ωCPO (D₂ i)]
  (f : ∀ i, D₁ i →c D₂ i) : (∀ i, D₁ i) →c (∀ i, D₂ i) where
  toFun arrow i := f i (arrow i)
  monotone' := by
    intro a b h i
    mono
    apply h
  continuous' := by
    intro F i
    exact (f i).continuous' _

@[simp] def map_apply {I: Type u} {D₁: I → Type v} {D₂: I → Type w}
  [∀ i:I, ωCPO (D₁ i)] [∀ i, ωCPO (D₂ i)]
  (f : ∀ i, D₁ i →c D₂ i) (p: ∀ i, D₁ i) (i: I) :
  map f p i = f i (p i) := Eq.refl _

def lift {I: Type u} {J: Type v} {D: I → Type v} [inst: ∀ i, ωCPO (D i)]
  (f: J → I) : (∀ i, D i) →c (∀ j, D (f j)) where
  toFun p j := p (f j)
  monotone' := by
    intro a b h j
    apply h
  continuous' := by
    intro F j
    simp only [lub, OrderHom.comp_coe, Function.comp_apply, le_refl]

@[simp] def lift_apply {I: Type u} {J: Type v} (D: I → Type v) [∀ i, ωCPO (D i)]
  (f: J → I) (p: ∀ i, D i) (j: J) : lift f p j = p (f j) := Eq.refl _

end ωCPO
