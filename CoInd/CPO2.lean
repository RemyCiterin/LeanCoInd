import Mathlib.Tactic.Monotonicity.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.BoundedOrder


#check Bot

class Mono {α: Type u₁} {β: Type u₂} (f: α → β) [Preorder α] [Preorder β] where
  monotone' : Monotone f

instance id.Mono {α: Type u} [Preorder α] : Mono (@id α) where
  monotone' := by
    intro x y h
    rw [id, id]
    assumption

@[mono] theorem Mono.mono {α: Type u₁} {β: Type u₂} (f: α → β) [Preorder α] [Preorder β]
  [inst:Mono f] : ∀ x y, x ≤ y → f x ≤ f y := inst.monotone'

instance Function.Comp.Mono {α: Type u₁} {β: Type u₂} {γ: Type u₃} [Preorder α] [Preorder β] [Preorder γ]
  (f: β → γ) (g: α → β) [Mono f] [Mono g] : Mono (f ∘ g) where
  monotone' := by
    intro a b h
    simp [Function.comp]
    mono

class ωCPO (D: Type u) extends Preorder D, Bot D where
  bot_le : ∀ x:D, ⊥ ≤ x
  lub : ∀ (f: Nat → D) [Mono f], D
  le_lub : ∀ {f: Nat → D} [Mono f] {n: Nat}, f n ≤ lub f
  lub_le : ∀ {f: Nat → D} [Mono f] {x: D}, (∀ n, f n ≤ x) → lub f ≤ x


namespace ωCPO
open ωCPO

variable {D₁: Type u₁} [inst₁: ωCPO D₁]
variable {D₂: Type u₂} [inst₂: ωCPO D₂]
variable {D₃: Type u₃} [inst₃: ωCPO D₃]
variable {D₄: Type u₄} [inst₄: ωCPO D₄]

@[mono]
theorem le_lub' (f: ℕ → D₁) [Mono f] (n: ℕ) : f n ≤ lub f :=
  le_lub

@[mono]
theorem compose_lub (F : D₁ → D₂) (f : Nat → D₁) [Mono F] [Mono f] :
  lub (F ∘ f) ≤ F (lub f) := by
  apply lub_le
  intro n
  rw [Function.comp]
  mono

def Continuous (F: D₁ → D₂) [Mono F] :=
  ∀ (f: ℕ → D₁) [Mono f], F (lub f ) ≤ lub (F ∘ f)

class Cont (F: D₁ → D₂) extends Mono F where
  continuous' : Continuous F
--infixr:25 " →c " => Continuous

@[mono]
def Continuous.apply (F: D₁ → D₂) [Cont F] :
  ∀ (f: ℕ → D₁) [Mono f], F (lub f) ≤ lub (F ∘ f) :=
  Cont.continuous'

instance id.Cont (D: Type u) [ωCPO D] : Cont (@id D) where
  continuous' := by
    intro f _
    apply le_rfl

#check Function.comp.assoc
instance Function.comp.Cont (f: D₂ → D₃) (g: D₁ → D₂) [contf: Cont f] [contg: Cont g] :
  Cont (f ∘ g) where
  continuous' := by
    intro F monoF
    have := contf.continuous' (g ∘ F)
    apply LE.le.trans _ this
    apply contf.monotone'
    apply contg.continuous'

@[mono]
def comp.monotone_left {D₁: Type u₁} {D₂: Type u₂} [Preorder D₁] [Preorder D₂]
  (f g: D₂ → D₃) (h: D₁ → D₂) [Mono f] [Mono g] [Mono h] : f ≤ g → f ∘ h ≤ g ∘ h :=
  λ h₁ x => h₁ (h x)

@[mono]
def comp.monotone_right {D₁: Type u₁} {D₂: Type u₂} [Preorder D₁] [Preorder D₂]
  (f: D₂ → D₃) (g h: D₁ → D₂) [Mono f] [Mono g] [Mono h] : g ≤ h → f ∘ g ≤ f ∘ h :=
  λ h₁ x => Mono.monotone' (h₁ x)

#check lub

instance {A: Type u₀} (f: Nat → (A → D₁)) [monof: Mono f] (x: A) : Mono fun n => f n x where
  monotone' := by
    intro a b h
    apply monof.monotone' h


instance {A: Type u₀} : ωCPO (A → D₁) where
  bot_le (f: A → D₁) x := inst₁.bot_le (f x)

  lub (f: Nat → (A → D₁)) [monof: Mono f] := λ (x:A) =>
    @lub D₁ inst₁ (λ n => f n x) ⟨λ n m h₁ => monof.monotone' h₁ x⟩

  lub_le := by
    intro f monof F h₁ x
    apply lub_le
    intro n
    apply h₁ n

  le_lub := by
    intro f monof n x
    apply LE.le.trans _ (@le_lub _ _ _ _ n)
    apply le_refl

@[mono]
def lub.monotone (f g: Nat → D₁) [Mono f] [Mono g] : f ≤ g → lub f ≤ lub g := by
  intro h
  apply lub_le
  intro n
  apply (h n).trans
  mono

-- TODO: show that if "f:Nat → (A → D)" and "∀ x, Mono f", then "lub f" is monotone
-- TODO: show that if "f:Nat → (A → D)" and "∀ x, Cont f", then "lub f" is continuous

#check bot_le

#print ωCPO
#print toBot
#print Bot
#print OrderBot

instance Prod.fst.mono {α : Type u} {β: Type v} [Preorder α] [Preorder β] : Mono (@Prod.fst α β) where
  monotone' := by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk_le_mk] at h
    exact h.1

instance Prod.snd.mono {α : Type u} {β: Type v} [Preorder α] [Preorder β] : Mono (@Prod.snd α β) where
  monotone' := by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk_le_mk] at h
    exact h.2

instance Prod.mk.mono {α : Type u} {β: Type v} [Preorder α] [Preorder β] : Mono (@Prod.mk α β) where
  monotone' := by
    intro a b h c
    rw [Prod.mk_le_mk]
    trivial

instance Prod.mk.mono_app {α : Type u} {β: Type v} (x: α) [Preorder α] [Preorder β]
  : Mono (@Prod.mk α β x) where
  monotone' := by
    intro a b h
    rw [Prod.mk_le_mk]
    trivial

instance : ωCPO (D₁ × D₂) where
  bot_le
  | (x, y) => by
    constructor
    . apply bot_le
    . apply bot_le

  lub (f: Nat → D₁ × D₂) := (inst₁.lub (Prod.fst ∘ f), inst₂.lub (Prod.snd ∘ f))

  le_lub := by
    intro f monof n
    have : f n = ((Prod.fst ∘ f) n, (Prod.snd ∘ f) n) := Eq.refl _
    rw [this]
    constructor
    . apply @le_lub _ _ (Prod.fst ∘ f)
    . apply @le_lub _ _ (Prod.snd ∘ f)

  lub_le := by
    intro f monof ⟨x, y⟩ h₁
    constructor
    . apply lub_le
      intro n
      apply (h₁ n).1
    . apply lub_le
      intro n
      apply (h₁ n).2

instance : Cont (@Prod.fst D₁ D₂) where
  continuous' := by
    intro f monof
    simp only [lub, le_refl]

instance : Cont (@Prod.snd D₁ D₂) where
  continuous' := by
    intro f monof
    simp only [lub, le_refl]

instance {α: Type u} [Preorder α] {x: D₂} : Mono (λ _:α => x) where
  monotone' := by
    intro _ _ _
    apply le_refl _

instance : Cont (@Prod.mk D₁ D₂) where
  continuous' := by
    intro f monof x
    rw [Prod.mk_le_mk]
    simp only [lub, Function.comp]
    have : Prod.fst ∘ (λ n => (f n, x)) = f := refl _
    constructor
    . apply lub.monotone
    . sorry




end ωCPO
