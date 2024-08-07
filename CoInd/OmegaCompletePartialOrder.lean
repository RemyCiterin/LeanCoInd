import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.Linarith
import CoInd.Tactic

open OmegaCompletePartialOrder


@[simp] def OrderHom.mk_apply {α: Type u} {β: Type v} [Preorder α] [Preorder β]
  (f: α → β) (hf: Monotone f) (x: α) : (OrderHom.mk f hf) x = f x := rfl

-- define projections, map and lift operations over Pi types
namespace Pi

variable {α: Type u₁} {α': Type u₂}
variable {β: α → Type u₃} [(a : α) → OmegaCompletePartialOrder (β a)]
variable {γ: α → Type u₄} [(a : α) → OmegaCompletePartialOrder (γ a)]


@[simps! apply]
def OmegaCompletePartialOrder.proj (a: α) : ((a: α) → β a) →𝒄 (β a) where
  toFun p := p a
  monotone' := λ _ _ h₁ => h₁ a
  cont _ := rfl


@[simps! apply]
def OmegaCompletePartialOrder.map (f:(a: α) → β a →𝒄 γ a) : (∀ a, β a) →𝒄 (∀ a, γ a) where
  toFun p a := f a (p a)
  monotone' := λ x y h₁ a => (f a).monotone' (h₁ a)
  cont := by
    intro c
    funext a
    apply (f a).cont

@[simps! apply]
def OmegaCompletePartialOrder.lift (f: α' → α) : (∀ a, β a) →𝒄 (∀ a, β (f a)) where
  toFun p a := p (f a)
  monotone' _ _ h₁ _ := h₁ _
  cont _ := rfl

end Pi

@[simp]
def OmegaCompletePartialOrder.OrderHom.fix.iterFun
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α → α) : ℕ → α
| n+1 => f (iterFun f n)
| 0 => ⊥

def OmegaCompletePartialOrder.OrderHom.fix.iterFun_le_succ
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →o α) (n: ℕ) : iterFun f n ≤ iterFun f (n+1) := by
  induction n with
  | zero =>
    apply bot_le
  | succ n h₁ =>
    apply f.monotone'
    exact h₁

def OmegaCompletePartialOrder.OrderHom.fix.iterFun_mono
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →o α) : Monotone (iterFun f) := by
  intro a b h₁
  induction h₁ with
  | refl =>
    apply le_refl
  | step _ h₂ =>
    apply h₂.trans
    apply iterFun_le_succ

instance {α: Type u} [Preorder α] : Preorder (Chain α) :=
  inferInstanceAs (Preorder (ℕ →o α))

@[simps! coe]
def OmegaCompletePartialOrder.OrderHom.fix.iter
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  : (α →o α) →o (Chain α) where
  toFun f := ⟨iterFun f, iterFun_mono f⟩
  monotone' := by
    intro f g h₁ n
    induction n with
    | zero =>
      apply bot_le
    | succ n h =>
      apply (f.monotone' h).trans
      apply h₁


def OmegaCompletePartialOrder.OrderHom.fix
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  : (α →o α) →o α where
  toFun f := ωSup (fix.iter f)
  monotone' := by
    intro f g h₁
    apply ωSup_le
    intro n
    apply le_trans _ (le_ωSup _ n)
    induction n with
    | zero =>
      apply bot_le
    | succ n h =>
      simp only [fix.iter, fix.iterFun]
      apply (f.monotone' h).trans
      apply h₁

namespace OmegaCompletePartialOrder.OrderHom.fix
variable {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]

def unfold_mono (f: α →o α) : fix f ≤ f (fix f) := by
  apply ωSup_le
  intro n
  cases n with
  | zero =>
    apply bot_le
  | succ n =>
    apply f.monotone'
    apply le_ωSup (iter f)

def unfold_cont (f: α →𝒄 α) : fix f = f (fix f) := by
  suffices fix f = ωSup ((iter f).map f.toOrderHom) by
    conv =>
      lhs
      rw [this, ←f.cont]
      rfl
    rfl
  apply le_antisymm
  · apply ωSup_le
    intro n
    apply LE.le.trans _ (le_ωSup _ n)
    simp only [Chain.map_coe, Function.comp_apply]
    apply (iter f.toOrderHom).monotone' (show n ≤ n+1 by simp)
  · apply ωSup_le
    intro n
    apply le_ωSup (iter f.toOrderHom) (n+1)

def IsLUB (f: α →o α) (x: α) (hyp: f x = x) : fix f ≤ x := by
  apply ωSup_le
  intro n
  induction n with
  | zero =>
    apply bot_le
  | succ n h =>
    rw [←hyp]
    apply f.monotone'
    assumption

end OmegaCompletePartialOrder.OrderHom.fix

def OmegaCompletePartialOrder.OrderHom.fix'
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  : (α →𝒄 α) →o α := fix.comp ContinuousHom.toMono

#print Continuous

/-
  Prove that the fixpoint operation over continuous functions is
  itself a continuous function
-/
theorem OmegaCompletePartialOrder.OrderHom.fix_count
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (c: Chain (α →𝒄 α)) : fix' (ωSup c) ≤ ωSup (c.map fix') := by
  apply ωSup_le
  intro n
  induction n with
  | zero =>
    apply bot_le
  | succ n h₁ =>
    simp only [fix.iter, fix.iterFun]
    apply ((ωSup c).monotone' h₁).trans
    have :
      (ωSup c).toFun (ωSup (c.map fix')) = ωSup ((c.map fix').map (ωSup c).toOrderHom)
      := (ωSup c).cont (c.map fix')
    rw [this]
    apply ωSup_le
    intro m
    apply ωSup_le
    intro k
    cases Nat.le_or_le m k with
    | inl h =>
      apply ((c k).monotone' (fix'.monotone' (c.monotone' h))).trans
      calc
        _ = (fix (c k : α →o α)) := by
          rw [fix.unfold_cont (c k)]
          rfl
        _ ≤ _ := by
          apply le_ωSup (c.map fix')
    | inr h =>
      apply (c.monotone' h (fix' (c m))).trans
      calc
        _ = (fix (c m: α →o α)) := by
          rw [fix.unfold_cont (c m)]
          rfl
        _ ≤ _ := by
          apply le_ωSup (c.map fix') m

/-
  A fixpoint operation over continuous function as a continuous function
-/
@[simps! apply]
def OmegaCompletePartialOrder.ContinuousHom.fix
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  : (α →𝒄 α) →𝒄 α where
  toFun f := OrderHom.fix f
  monotone' := by
    intro a b h
    apply OrderHom.fix.monotone' h
  cont := by
    intro c
    suffices OrderHom.fix' (ωSup c) = ωSup (c.map OrderHom.fix') by
      exact this
    apply le_antisymm
    · apply OrderHom.fix_count
    · apply ωSup_le
      intro n
      apply ωSup_le
      intro m
      apply le_trans _ (le_ωSup _ m)
      induction m with
      | zero =>
        apply bot_le
      | succ m h =>
        apply ((c n).monotone' h).trans
        apply le_ωSup c n

#print ContinuousHom

/-
  The unfold theorem for continuous fixed point
-/
def OmegaCompletePartialOrder.ContinuousHom.fix.unfold
  {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]
  (f: α →𝒄 α) : fix f = f (fix f) :=
  OrderHom.fix.unfold_cont f

namespace OmegaCompletePartialOrder.Chain
variable {α: Type u} [OmegaCompletePartialOrder α]

@[simps! coe]
def filter (c: Chain α) (U: ℕ →o ℕ) : Chain α := c.comp U

-- ensure that an increasing seauence `c` filtred by `U` have a supremum less than
-- the supremum of `c`
def ωSup_filter (c: Chain α) (U: ℕ →o ℕ) : ωSup (filter c U) ≤ ωSup c := by
  apply ωSup_le
  intro n
  apply le_ωSup c (U n)

-- ensure that if an increasing sequance `c` is filtred with an injective function `U`, then
-- the supremum of `c` and `c.filter u` are equals
def ωSup_filter_inj (c: Chain α) (U: ℕ →o ℕ) (inj: Function.Injective U) : ωSup (c.filter U) = ωSup c := by
  apply le_antisymm
  · apply ωSup_filter
  · apply ωSup_le
    intro n
    have : ∀ n, n ≤ U n := by
      intro n
      induction n with
      | zero =>
        apply Nat.zero_le
      | succ n h =>
        have := Nat.succ_le_succ h
        apply this.trans
        have := @Nat.lt_iff_le_and_ne (U n) (U (.succ n))
        apply this.mpr
        constructor
        · apply U.monotone
          simp_arith
        · intro h
          specialize inj h
          cases inj
    apply le_trans _ (le_ωSup (filter c U) n)
    apply c.monotone'
    apply this

end OmegaCompletePartialOrder.Chain

def OmegaCompletePartialOrder.IsAdmissible {α: Type u} [OmegaCompletePartialOrder α] (S: Set α) :=
  ∀ (c: Chain α), (∀ n, S (c n)) → S (ωSup c)

structure OmegaCompletePartialOrder.Admissible
  (α: Type u) [OmegaCompletePartialOrder α] [OrderBot α] where
  toSet : Set α
  admissible': IsAdmissible toSet
  contain_bot: ⊥ ∈ toSet

attribute [coe] Admissible.toSet

namespace OmegaCompletePartialOrder.Admissible
variable {α: Type u} [OmegaCompletePartialOrder α] [OrderBot α]

instance instFunLike : FunLike (Admissible α) α Prop where
  coe := toSet
  coe_injective' := by
    intro a b h₁
    cases a
    cases b
    rw [Admissible.mk.injEq]
    exact h₁

instance : CoeFun (Admissible α) fun _ => α → Prop := ⟨toSet⟩

instance : Membership α (Admissible α) :=
  ⟨λ x s => s x⟩

@[refinment_type] def admissible (p: Admissible α) (c: Chain α) :
  (∀ n, c n ∈ p) → ωSup c ∈ p := p.admissible' c

-- Conjunction of two properties
def And (lhs rhs: Admissible α) : Admissible α where
  toSet x := x ∈ lhs ∧ x ∈ rhs

  admissible' := by
    intro c h₁
    constructor
    · apply lhs.admissible'
      intro n
      specialize h₁ n
      exact h₁.left
    · apply rhs.admissible'
      intro n
      specialize h₁ n
      exact h₁.right

  contain_bot := by
    constructor
    · exact lhs.contain_bot
    · exact rhs.contain_bot

@[refinment_type] def And.intro (lhs rhs: Admissible α) (x: α) :
  x ∈ lhs → x ∈ rhs → x ∈ And lhs rhs := by
  intro a v
  constructor
  <;> assumption

def Or.prop (p: Admissible α) (c: Chain α) (n: Nat) (m: Nat) : Prop := p (c (n+m))

/-
Define an increasing and injective sequence such that if `p` hold infinitly many times
in `c`, then `p` hold for each elements of `sequence p c`
-/
noncomputable def Or.sequence (p: Admissible α) (c: Chain α) : Nat → Nat
| n+1 =>
  let m := sequence p c n
  (m+1) + Classical.epsilon (prop p c (m + 1))
| 0 => Classical.epsilon (prop p c 0)

theorem Or.sequence.strict_mono' (p: Admissible α) (c: Chain α) (n: ℕ) :
  sequence p c n < sequence p c (n+1) := by
  rw [sequence]
  simp_arith

theorem Or.sequence.strict_mono (p: Admissible α) (c: Chain α) (n m: ℕ) (h₁: n < m) :
  sequence p c n < sequence p c m := by
  induction h₁ with
  | refl =>
    apply strict_mono'
  | step _ h₂ =>
    apply h₂.trans
    apply strict_mono'

theorem Or.sequence.inj (p: Admissible α) (c: Chain α) : Function.Injective (sequence p c) := by
  intro a b h₁
  cases Nat.le_or_le a b with
  | inl h₂ =>
    cases le_iff_lt_or_eq.mp h₂ with
    | inl h₃ =>
      have := strict_mono p c a b h₃
      rw [h₁] at this
      simp at this
    | inr h₃ =>
      assumption
  | inr h₂ =>
    cases le_iff_lt_or_eq.mp h₂ with
    | inl h₃ =>
      have := strict_mono p c b a h₃
      rw [h₁] at this
      simp at this
    | inr h₃ =>
      cases h₃
      rfl

noncomputable def Or.sequence' (p: Admissible α) (c: Chain α) : ℕ →o ℕ where
  toFun := sequence p c
  monotone' := by
    intro a b h₁
    induction h₁ with
    | refl =>
      apply le_refl
    | step _ h₂ =>
      apply h₂.trans
      simp only [sequence]
      linarith

#print OrderHom.comp

#check Classical.epsilon_spec

def Or.sequence_spec (p: Admissible α) (c: Chain α) :
  (∀ n, ∃ m, p (c (n + m))) → ∀ n, p (c.filter (Or.sequence' p c) n) := by
  intro h₁ n
  cases n with
  | zero =>
    conv =>
      rhs
      rw [Chain.filter, OrderHom.comp, OrderHom.coe_mk, Function.comp_apply]
      rw [sequence', OrderHom.coe_mk, sequence]
      rw [←Nat.zero_add (Classical.epsilon (prop p c 0))]
      unfold prop

    apply @Classical.epsilon_spec _ (λ m => p (c (0 + m)))
    specialize h₁ 0
    assumption
  | succ m =>
    simp only [Chain.filter, sequence', sequence, prop]
    apply @Classical.epsilon_spec _ (λ m' => p <| c <| sequence p c m + 1 + m')
    apply h₁

def Or.pigeonhole (p q: Admissible α) (c: Chain α) (h₁: ∀ n, p (c n) ∨ q (c n)) :
  (∀ n, ∃ m, p (c (n+m))) ∨ (∀ n, ∃ m, q (c (n+m))) := by
  by_cases h:(∀ n, ∃ m, p (c (n+m)))
  · apply Or.inl h
  · apply Or.inr
    intro n
    conv at h =>
      rw [not_forall]
      rhs; intro k
      rw [not_exists]
      rfl
    have ⟨k, h⟩ := h
    specialize h n
    rw [add_comm] at h
    specialize h₁ (n+k)
    exists k
    simp only [h, false_or] at h₁
    assumption

/- Disjunction of two admissible properties -/
def Or (lhs rhs: Admissible α) : Admissible α where
  toSet x := x ∈ lhs ∨ x ∈ rhs

  contain_bot := by
    apply Or.inl
    exact lhs.contain_bot

  admissible' := by
    intro c h₁

    let lhsS := Or.sequence' lhs c
    let rhsS := Or.sequence' rhs c
    let lhsC := c.filter lhsS
    let rhsC := c.filter rhsS
    have lhsI : ωSup lhsC = ωSup c := Chain.ωSup_filter_inj c lhsS (Or.sequence.inj _ _)
    have rhsI : ωSup rhsC = ωSup c := Chain.ωSup_filter_inj c rhsS (Or.sequence.inj _ _)
    conv =>
      congr
      . rw [←lhsI]
      . rw [←rhsI]
    cases Or.pigeonhole lhs rhs c h₁ with
    | inl h₂ =>
      apply Or.inl
      apply lhs.admissible'
      apply Or.sequence_spec lhs c h₂
    | inr h₂ =>
      apply Or.inr
      apply rhs.admissible'
      apply Or.sequence_spec rhs c h₂


def Forall {β: Sort v} (p: β → Admissible α) : Admissible α where
  toSet x := ∀ y, x ∈ p y
  contain_bot := by
    intro y
    apply (p y).contain_bot
  admissible' := by
    intro c h₁ y
    apply (p y).admissible'
    intro n
    apply h₁

@[refinment_type] def Forall.intro {β: Sort v} (p: β → Admissible α) (x: α) :
  (∀ y, x ∈ p y) → x ∈ Forall p := λ h => h

@[refinment_type] def contain_bot' (p: Admissible α) : ⊥ ∈ p := p.contain_bot

-- If a proposition `p` is admissible then if is enough to show that `p` is stable
-- by `f` to show that `Fix f` ensure `p`
@[refinment_type] def Fix_thm (p: Admissible α) (f: α →o α) (IsInv: ∀ x, x ∈ p → f x ∈ p) : OrderHom.fix f ∈ p := by
  apply p.admissible' (OrderHom.fix.iter f)
  intro n
  induction n with
  | zero =>
    apply p.contain_bot
  | succ n h₁ =>
    exact IsInv (OrderHom.fix.iter f n) h₁

@[refinment_type] def FixCont_thm (p: Admissible α) (f: α →𝒄 α) (IsInv: ∀ x, x ∈ p → f x ∈ p) : ContinuousHom.fix f ∈ p :=
  Fix_thm p f IsInv

-- prove that a "lustre node" verify a property if this property is inductive
def NodeFix_thm {β: Type v}
  [OmegaCompletePartialOrder β] [OrderBot β]
  (node_eqs: α →𝒄 β →𝒄 β)
  (p: Admissible α) (q: Admissible β)
  (IsInv: ∀ x y, x ∈ p → y ∈ q → node_eqs x y ∈ q)
  (x: α) (h₁: x ∈ p) : ContinuousHom.fix.comp node_eqs x ∈ q := by
  apply Fix_thm
  intro y h₂
  apply IsInv <;> assumption

#check ContinuousHom

end OmegaCompletePartialOrder.Admissible



namespace OmegaCompletePartialOrder.ContinuousHom.Prod
variable {α: Type u} [OmegaCompletePartialOrder α]
variable {β: Type v} [OmegaCompletePartialOrder β]
variable {γ: Type w} [OmegaCompletePartialOrder γ]

@[simps! apply]
def fst : α × β →𝒄 α where
  toFun p := p.fst
  monotone' := OrderHom.fst.monotone'
  cont := by
    intro chain
    rfl

@[simps! apply]
def snd : α × β →𝒄 β where
  toFun p := p.snd
  monotone' := OrderHom.snd.monotone'
  cont := by
    intro chain
    rfl

@[simps! apply]
def prod (f: α →𝒄 β) (g: α →𝒄 γ) : α →𝒄 β × γ where
  toFun x := (f x, g x)
  monotone' := (OrderHom.prod f.toOrderHom g.toOrderHom).monotone'
  cont := by
    intro chain
    rw [Prod.mk.injEq]
    constructor
    · apply f.cont
    · apply g.cont

#check Chain.zip
#check OrderHom.const
#check le_ωSup

@[simps! apply]
def curry.hom (f: α × β →𝒄 γ) : α →𝒄 β →𝒄 γ where
  toFun x := f.comp (prod (const x) id)
  monotone' := by
    intro a b h₁ x
    apply f.monotone'
    constructor
    · apply h₁
    · apply le_refl
  cont := by
    intro chain
    apply ContinuousHom.ext
    intro x
    simp
    calc
      _ = f (ωSup (Chain.zip chain (OrderHom.const _ x))) := by
        apply congrArg
        rw [Prod.mk.injEq]
        constructor
        · rfl
        · apply le_antisymm
          · apply le_ωSup (OrderHom.const ℕ x) 0
          · apply ωSup_le
            intro _
            apply le_refl
      _ = ωSup (Chain.map (Chain.zip chain (OrderHom.const _ x)) f) := f.cont _
      _ = _ := rfl

@[simps! apply]
def curry.inv (f: α →𝒄 β →𝒄 γ) : α × β →𝒄 γ where
  toFun p := f p.fst p.snd
  monotone' := by
    intro ⟨x, y⟩ ⟨z, t⟩ ⟨h₁, h₂⟩
    apply ((f x).monotone' h₂).trans
    apply f.monotone'
    assumption
  cont := by
    intro chain
    calc
      _ = f (ωSup (chain.map OrderHom.fst)) (ωSup (chain.map OrderHom.snd)) := by rfl
      _ = ωSup ((chain.map OrderHom.snd).map <| f (ωSup (chain.map OrderHom.fst))) := by
        rw [(f _).continuous]
      _ = ωSup ((chain.map OrderHom.snd).map <| ωSup ((chain.map OrderHom.fst).map (toMono.comp f))) := by
        rw [f.continuous]
        rfl
      _ = _ := by
        simp only [ωSup, Prod.ωSup, OmegaCompletePartialOrder.ωSup, Chain.map,OrderHom.comp, Function.comp]
        apply le_antisymm
        <;> apply ωSup_le
        <;> intro n
        · apply ωSup_le
          intro m
          cases Nat.le_or_le n m with
          | inl h =>
            rw [OrderHom.mk_apply]
            apply ((f (chain m).fst).monotone (chain.monotone h).right).trans
            apply le_trans _ (le_ωSup _ m)
            apply le_refl
          | inr h =>
            apply (f.monotone (chain.monotone h).left _).trans
            apply le_trans _ (le_ωSup _ n)
            apply le_refl
        · apply le_trans _ (le_ωSup _ n)
          apply le_trans _ (le_ωSup _ n)
          apply le_refl

@[simps! apply symm_apply]
def curry : (α × β →𝒄 γ) ≃o (α →𝒄 β →𝒄 γ) where
  toFun := curry.hom
  invFun := curry.inv

  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {f g} := by
    constructor
    <;> intro h
    · intro ⟨x, y⟩
      exact h x y
    · intro x y
      exact h (x, y)

end OmegaCompletePartialOrder.ContinuousHom.Prod


@[to_additive existing OmegaCompletePartialOrder.Cat]
def OmegaCompletePartialOrder.Cat : Type (u+1) :=
  CategoryTheory.Bundled OmegaCompletePartialOrder

#check DFunLike.coe

namespace OmegaCompletePartialOrder.Cat
variable {α: Type u} [OmegaCompletePartialOrder α]
variable {β: Type v} [OmegaCompletePartialOrder β]
variable {γ: Type w} [OmegaCompletePartialOrder γ]


open CategoryTheory

#print BundledHom

instance bundledHom : BundledHom @ContinuousHom where
  toFun {α β} X Y f := f
  id := @ContinuousHom.id
  comp := @ContinuousHom.comp

deriving instance LargeCategory for OmegaCompletePartialOrder.Cat

instance concreteCategory : ConcreteCategory Cat :=
  inferInstanceAs <| ConcreteCategory (Bundled OmegaCompletePartialOrder)

instance : CoeSort Cat Type* where
  coe X := X.α

instance omegaCompletePartialOrderUnbundled (X : Cat) : OmegaCompletePartialOrder X :=
  X.str

instance instFunLike (X Y : Cat) : FunLike (X ⟶  Y) X Y :=
  inferInstanceAs <| FunLike (X →𝒄 Y) X Y

instance omegaCompletePartialOrder_coe (X : Cat) : OmegaCompletePartialOrder X :=
  X.str

@[instance] abbrev omegaCompletePartialOrder_forget
    (X : Cat) : OmegaCompletePartialOrder <| (forget Cat).obj X :=
  X.str

theorem id_app (X : Cat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

theorem comp_app {X Y Z : Cat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[simp] theorem coe_id (X : Cat.{u}) : (𝟙 X : X → X) = id := rfl

@[simp] theorem coe_comp {X Y Z : Cat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma hom_inv_id_apply {X Y : Cat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  DFunLike.congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : Cat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  DFunLike.congr_fun f.inv_hom_id y

def of (X : Type u) [OmegaCompletePartialOrder X] : Cat :=
  ⟨X, inferInstance⟩

@[simp]
theorem coe_of (X : Type u) [OmegaCompletePartialOrder X] : (of X : Type u) = X := rfl

@[simp] theorem coe_of_of {X Y : Type u} [OmegaCompletePartialOrder X] [OmegaCompletePartialOrder Y]
    {f : X →𝒄 Y} {x} :
    @DFunLike.coe (Cat.of X ⟶  Cat.of Y) ((CategoryTheory.forget Cat).obj (Cat.of X))
      (fun _ ↦ (CategoryTheory.forget Cat).obj (Cat.of Y)) ConcreteCategory.instFunLike
      f x =
    @DFunLike.coe (X →𝒄 Y) X
      (fun _ ↦ Y) _
      f x :=
  rfl

instance : OmegaCompletePartialOrder Empty where
  le x y := x = y
  le_refl x := rfl
  le_trans x y z h₁ h₂ := Trans.trans h₁ h₂
  le_antisymm x := x.elim
  ωSup c := (c 0).elim
  le_ωSup c n := (c n).elim
  ωSup_le c := (c 0).elim

instance inhabited : Inhabited Cat :=
  ⟨Cat.of Empty⟩

lemma hom_apply {X Y : Cat} (f : X ⟶  Y) (x : X) : f x = (f : X →𝒄 Y) x := rfl

instance : OmegaCompletePartialOrder Unit where
  ωSup _ := .unit
  le_ωSup _ _ := le_refl _
  ωSup_le _ _ _ := le_refl _


@[simps! apply]
def whiskerLeft (X: Cat) {Y Z: Cat} (f: Y ⟶  Z) : of (X × Y) ⟶  of (X × Z) where
  toFun := λ (x, y) => (x, f y)
  monotone' := by
    intro ⟨a, b⟩ ⟨c, d⟩ h₁
    rw [Prod.mk_le_mk] at h₁
    rw [Prod.mk_le_mk]
    constructor
    · exact h₁.left
    · apply f.monotone
      exact h₁.right
  cont := by
    intro c
    simp only [coe_of, OrderHom.coe_mk, Prod.instOmegaCompletePartialOrder_ωSup_fst,
      Prod.instOmegaCompletePartialOrder_ωSup_snd]
    rw [f.continuous (c.map OrderHom.snd)]
    rfl

@[simps! apply]
def whiskerRight {X Y: Cat} (f: X ⟶  Y) (Z: Cat) : of (X × Z) ⟶  of (Y × Z) where
  toFun := (λ (x, y) => (f x, y))
  monotone' := by
    intro ⟨a, b⟩ ⟨c, d⟩ h₁
    rw [Prod.mk_le_mk] at h₁
    rw [Prod.mk_le_mk]
    constructor
    · apply f.monotone
      exact h₁.left
    · exact h₁.right
  cont := by
    intro c
    simp only [coe_of, OrderHom.coe_mk, Prod.instOmegaCompletePartialOrder_ωSup_snd,
      Prod.instOmegaCompletePartialOrder_ωSup_fst]
    rw [f.continuous (c.map OrderHom.fst)]
    rfl

@[simps! apply]
def tensorHom {X₁ Y₁ X₂ Y₂: Cat} (f: X₁ ⟶  Y₁) (g: X₂ ⟶  Y₂) : of (X₁ × X₂) ⟶  of (Y₁ × Y₂) where
  toFun := λ (x, y) => (f x, g y)
  monotone' := by
    intro ⟨a, b⟩ ⟨c, d⟩ h₁
    rw [Prod.mk_le_mk] at h₁
    rw [Prod.mk_le_mk]
    constructor
    · apply f.monotone
      exact h₁.left
    · apply g.monotone
      exact h₁.right
  cont := by
    intro c
    simp only [coe_of, OrderHom.coe_mk, Prod.instOmegaCompletePartialOrder_ωSup_snd,
      Prod.instOmegaCompletePartialOrder_ωSup_fst]
    rw [f.continuous (c.map OrderHom.fst)]
    rw [g.continuous (c.map OrderHom.snd)]
    rfl

@[simps! apply]
def associator.hom (X Y Z: Cat) : (X × Y) × Z →𝒄 X × Y × Z where
  toFun := (λ ((x, y), z) => (x, (y, z)))
  monotone' := by
    intro ((x, y), z) ((x', y'), z') ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨h₁, h₂, h₃⟩
  cont := by
    intro c
    rfl

@[simps! apply]
def associator.inv (X Y Z: Cat) : X × Y × Z →𝒄 (X × Y) × Z where
  toFun := (λ (x, (y, z)) => ((x, y), z))
  monotone' := by
    intro ⟨x, y, z⟩ ⟨x', y', z'⟩ ⟨h₁, h₂, h₃⟩
    exact ⟨⟨h₁, h₂⟩, h₃⟩
  cont := by
    intro c
    rfl

@[simps! hom inv]
def associator (X Y Z: Cat) :
  of ((X × Y) × Z) ≅ of (X × Y × Z) where
  hom := associator.hom X Y Z
  inv := associator.inv X Y Z
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simps! apply]
def leftUnitor.hom (X: Cat) : Unit × X →𝒄 X where
  toFun := (λ (_, x) => x)
  monotone' := by
    intro (_, x) (_, y) ⟨_, h⟩
    exact h
  cont := by
    intro c
    rfl

@[simps! apply]
def leftUnitor.inv (X: Cat) : X →𝒄 Unit × X where
  toFun := (λ x => ((), x))
  monotone' := by
    intro x y h
    exact ⟨le_refl (), h⟩
  cont := by
    intro c
    rfl

@[simps! hom inv]
def leftUnitor (X: Cat) :
  of (of Unit × X) ≅ X where
  hom := leftUnitor.hom X
  inv := leftUnitor.inv X

  inv_hom_id := rfl
  hom_inv_id := rfl

@[simps! apply]
def rightUnitor.hom (X: Cat) : X × Unit →𝒄 X where
  toFun := (λ (x, _) => x)
  monotone' := by
    intro (x, _) (y, _) ⟨h, _⟩
    exact h
  cont := by
    intro c
    rfl


@[simps! apply]
def rightUnitor.inv (X: Cat) : X →𝒄 X × Unit where
  toFun := (λ x => (x, ()))
  monotone' := by
    intro x y h
    exact ⟨h, le_refl ()⟩
  cont := by
    intro c
    rfl

@[simps! inv hom]
def rightUnitor (X: Cat) :
  of (X × of Unit) ≅ X where
  hom := rightUnitor.hom X
  inv := rightUnitor.inv X

  inv_hom_id := rfl
  hom_inv_id := rfl

-- prof that the category of ω-CPO is monoidal
instance : MonoidalCategory Cat where
  tensorObj X Y := Cat.of <| X × Y

  whiskerLeft := whiskerLeft

  whiskerRight := whiskerRight

  tensorHom := tensorHom

  tensorUnit := Cat.of Unit

  associator := associator

  leftUnitor := leftUnitor

  rightUnitor := rightUnitor

  tensorHom_def _ _ := rfl

  tensor_id _ _ := rfl

  tensor_comp _ _ _ _ := rfl

  whiskerLeft_id _ _ := rfl

  id_whiskerRight _ _ := rfl

  associator_naturality _ _ _ := rfl

  leftUnitor_naturality _ := rfl

  rightUnitor_naturality _ := rfl

  pentagon _ _ _ _ := rfl

  triangle _ _ := rfl


--instance hasFiniteProducts : Limits.HasFiniteProducts Cat.{u} where
--  out n := ⟨λ F => ⟨⟨⟨⟨_, _⟩, _⟩⟩⟩⟩
end OmegaCompletePartialOrder.Cat
