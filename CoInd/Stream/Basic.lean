import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils
--import CoInd.Stream.LTLBase
import CoInd.Eqns


import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq

universe u v w u₀ u₁ u₂

variable {α : Type u}

#print Container
#print Container.Obj

def streamC (α: Type u) : Container := ⟨α, fun _ => PUnit⟩

def stream (α: Type u) := Container.M (streamC α)

def stream.head (s: stream α) : α := s.destruct.fst

def stream.tail (s: stream α) : stream α := s.destruct.snd PUnit.unit

def stream.corec {β: Type v} (f: β → α × β) (x₀: β) : stream α :=
  Container.M.corec (λ x => let (a, b) := f x; ⟨a, λ _ => b⟩) x₀

@[simp] def stream.head_corec {β: Type v} (f: β → α × β) (x₀: β) :
  head (corec f x₀) = (f x₀).fst := by
  rfl

@[simp] def stream.tail_corec {β: Type v} (f: β → α × β) (x₀: β) :
  tail (corec f x₀) = corec f (f x₀).snd := by
  rfl

-- attribute [eqns stream.head_corec] stream.head

@[simp] def stream.next (s: stream α) : stream α := stream.tail s

def stream.cons (x: α) (s: stream α) : stream α := Container.M.construct ⟨x, fun _ => s⟩

@[simp] theorem stream.head_cons (x: α) (s: stream α) :
  head (cons x s) = x := by rfl

#check Container.M.destruct_construct

@[simp] theorem stream.tail_cons (x: α) (s: stream α) :
  tail (cons x s) = s := by
  simp only [cons, tail]
  rw [Container.M.destruct_construct]

@[simp] theorem stream.cons_head_tail (s: stream α) :
  cons (head s) (tail s) = s := by
  simp only [cons, head, tail]
  have : (fun _ => PSigma.snd (Container.M.destruct s) PUnit.unit) = s.destruct.snd := by rfl
  conv =>
    lhs
    rhs
    rhs
    rw [this]
    rfl
  rw [Container.M.construct_destruct]

theorem stream.bisim (r: stream α → stream α → Prop)
  (hyp: ∀ s₁ s₂, r s₁ s₂ → s₁.head = s₂.head ∧ r s₁.tail s₂.tail) :
  ∀ s₁ s₂, r s₁ s₂ → s₁ = s₂ := by
  intro s₁ s₂ h₁
  apply @Container.M.bisim _ r
  . intro x y h₂
    exists stream.head x
    exists λ _ => stream.tail x
    exists λ _ => stream.tail y
    constructor
    . rfl
    . constructor
      . specialize hyp x y h₂
        rw [hyp.1]
        rfl
      . intro _
        exact (hyp x y h₂).2
  assumption

@[simp] def stream.fby (s₁ s₂: stream α) : stream α :=
  cons (head s₁) s₂

def stream.const (x: α) : stream α := corec (λ u => (x, u)) Unit.unit

@[simp] theorem stream.head_const (x: α) :
  head (const x) = x := by rfl

@[simp] theorem stream.tail_const (x: α) :
  tail (const x) = const x := by rfl

def stream.first (s: stream α) : stream α := const (head s)

@[simp] def stream.first_first (s: stream α) :
  s.first.first = s.first := by rfl

@[simp] def stream.head_first (s: stream α) :
  s.first.head = s.head := by rfl

@[simp] def stream.tail_first (s: stream α) :
  s.first.tail = s.first := by rfl

@[simp] def stream.first_fby (s₁ s₂: stream α) :
  (s₁.fby s₂).first = s₁.first := by rfl

@[simp] def stream.tail_fby (s₁ s₂: stream α) :
  (s₁.fby s₂).tail = s₂ := by simp


instance : Functor stream where
  map f := stream.corec (λ s => ⟨f s.head, s.tail⟩)

@[simp] def stream.head_map (f: α → β) :
  ∀ s: stream α, (f <$> s).head = f s.head := by
  intro s
  simp only [Functor.map]
  rw [head_corec]

@[simp] def stream.tail_map (f: α → β) :
  ∀ s: stream α, (f <$> s).tail = f <$> s.tail := by
  intro s
  simp only [Functor.map]
  rw [tail_corec]

#check Prod

def stream.mkPair (s₁: stream α) (s₂: stream β) : stream (α × β) :=
  corec (λ (s₁, s₂) => ((s₁.head, s₂.head), (s₁.tail, s₂.tail))) (s₁, s₂)

@[simp] theorem stream.head_mkPair (s₁: stream α) (s₂: stream β) :
  head (mkPair s₁ s₂) = (s₁.head, s₂.head) := by rfl

@[simp] theorem stream.tail_mkPair (s₁: stream α) (s₂: stream β) :
  tail (mkPair s₁ s₂) = mkPair s₁.tail s₂.tail := by rfl

def stream.fst (s: stream (α × β)) : stream α :=
  corec (λ s => (s.head.fst, s.tail)) s

@[simp] theorem stream.head_fst (s: stream (α × β)) :
  s.fst.head = s.head.fst := by rfl

@[simp] theorem stream.tail_fst (s: stream (α × β)) :
  s.fst.tail = s.tail.fst := by rfl

def stream.snd (s: stream (α × β)) : stream β :=
  corec (λ s => (s.head.snd, s.tail)) s

@[simp] theorem stream.head_snd (s: stream (α × β)) :
  s.snd.head = s.head.snd := by rfl

@[simp] theorem stream.tail_snd (s: stream (α × β)) :
  s.snd.tail = s.tail.snd := by rfl

@[simp] theorem stream.mkPair_fst_snd (s: stream (α × β)) :
  mkPair (fst s) (snd s) = s := by
  apply bisim (λ s₁ s₂ => s₁ = mkPair s₂.fst s₂.snd)
  intro s₁ s₂ h₁
  constructor
  . rw [h₁]
    rfl
  . rw [h₁]
    rfl
  rfl

@[simp] theorem stream.fst_mkPair (s₁: stream α) (s₂: stream β) :
  (mkPair s₁ s₂).fst = s₁ := by
  apply bisim (λ s₁ s₂ => ∃ y: stream β, s₁ = (mkPair s₂ y).fst)
  . intro s₁ s₂ ⟨y, h₁⟩
    rw [h₁]
    constructor
    . rfl
    . exists y.tail
  exists s₂

@[simp] theorem stream.snd_mkPair (s₁: stream α) (s₂: stream β) :
  (mkPair s₁ s₂).snd = s₂ := by
  apply bisim (λ s₁ s₂ => ∃ y: stream α, s₁ = (mkPair y s₂).snd)
  . intro s₁ s₂ ⟨y, h₁⟩
    rw [h₁]
    constructor
    . rfl
    . exists y.tail
  exists s₁

abbrev stream.lift₂ (f: α → β → γ) (s₁: stream α) (s₂: stream β) : stream γ :=
  (λ (x, y) => f x y) <$> mkPair s₁ s₂


instance [HAdd α β γ] : HAdd (stream α) (stream β) (stream γ) where
  hAdd s₁ s₂ := stream.lift₂ HAdd.hAdd s₁ s₂

instance [HSub α β γ] : HSub (stream α) (stream β) (stream γ) where
  hSub s₁ s₂ := stream.lift₂ HSub.hSub s₁ s₂

instance [HMul α β γ] : HMul (stream α) (stream β) (stream γ) where
  hMul s₁ s₂ := stream.lift₂ HMul.hMul s₁ s₂

instance [HDiv α β γ] : HDiv (stream α) (stream β) (stream γ) where
  hDiv s₁ s₂ := stream.lift₂ HDiv.hDiv s₁ s₂

instance [HMod α β γ] : HMod (stream α) (stream β) (stream γ) where
  hMod s₁ s₂ := stream.lift₂ HMod.hMod s₁ s₂

instance [HAnd α β γ] : HAnd (stream α) (stream β) (stream γ) where
  hAnd s₁ s₂ := stream.lift₂ HAnd.hAnd s₁ s₂

instance [HOr α β γ] : HOr (stream α) (stream β) (stream γ) where
  hOr s₁ s₂ := stream.lift₂ HOr.hOr s₁ s₂

instance [HXor α β γ] : HXor (stream α) (stream β) (stream γ) where
  hXor s₁ s₂ := stream.lift₂ HXor.hXor s₁ s₂

@[simp] theorem stream.head_add [HAdd α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ + s₂) = s₁.head + s₂.head := by rfl
@[simp] theorem stream.head_sub [HSub α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ - s₂) = s₁.head - s₂.head := by rfl
@[simp] theorem stream.head_mul [HMul α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ * s₂) = s₁.head * s₂.head := by rfl
@[simp] theorem stream.head_div [HDiv α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ / s₂) = s₁.head / s₂.head := by rfl
@[simp] theorem stream.head_mod [HMod α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ % s₂) = s₁.head % s₂.head := by rfl
@[simp] theorem stream.head_and [HAnd α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ &&& s₂) = s₁.head &&& s₂.head := by rfl
@[simp] theorem stream.head_or  [HOr  α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ ||| s₂) = s₁.head ||| s₂.head := by rfl
@[simp] theorem stream.head_xor [HXor α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ ^^^ s₂) = s₁.head ^^^ s₂.head := by rfl

@[simp] theorem stream.tail_add [HAdd α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ + s₂) = s₁.tail + s₂.tail := by rfl
@[simp] theorem stream.tail_sub [HSub α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ - s₂) = s₁.tail - s₂.tail := by rfl
@[simp] theorem stream.tail_mul [HMul α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ * s₂) = s₁.tail * s₂.tail := by rfl
@[simp] theorem stream.tail_div [HDiv α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ / s₂) = s₁.tail / s₂.tail := by rfl
@[simp] theorem stream.tail_mod [HMod α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ % s₂) = s₁.tail % s₂.tail := by rfl
@[simp] theorem stream.tail_and [HAnd α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ &&& s₂) = s₁.tail &&& s₂.tail := by rfl
@[simp] theorem stream.tail_or  [HOr  α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ ||| s₂) = s₁.tail ||| s₂.tail := by rfl
@[simp] theorem stream.tail_xor [HXor α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ ^^^ s₂) = s₁.tail ^^^ s₂.tail := by rfl

#check GetElem.getElem

def stream.get (s: stream α) : Nat → α
| n+1 => s.tail.get n
| 0 => s.head

instance : GetElem (stream α) Nat α (λ _ _ => True) where
  getElem s n _ := s.get n

@[simp] theorem stream.get_succ (s: stream α) (n: Nat) :
  s[n+1] = s.tail[n] := by rfl

@[simp] theorem stream.get_zero (s: stream α) :
  s[0] = s.head := by rfl

@[simp] theorem stream.get_const (x: α) (n: Nat) :
  (const x)[n] = x := by
  induction n with
  | zero => rfl
  | succ n h =>
    simp only [get_succ, tail_const]
    assumption

@[simp] theorem stream.get_map (f: α → β) (s: stream α) (n: Nat) :
  (f <$> s)[n] = f s[n] := by
  induction n generalizing s with
  | zero => rfl
  | succ n h =>
    specialize h s.tail
    assumption

@[simp] theorem stream.get_mkPair (s₁: stream α) (s₂: stream β) (n: Nat) :
  (mkPair s₁ s₂)[n] = (s₁[n], s₂[n]) := by
  induction n generalizing s₁ s₂ with
  | zero => rfl
  | succ n h =>
    specialize h s₁.tail s₂.tail
    assumption

@[simp] theorem stream.get_fst (s: stream (α × β)) (n: Nat) :
  s.fst[n] = s[n].fst := by
  induction n generalizing s with
  | zero => rfl
  | succ n h =>
    specialize h s.tail
    assumption

@[simp] theorem stream.get_snd (s: stream (α × β)) (n: Nat) :
  s.snd[n] = s[n].snd := by
  induction n generalizing s with
  | zero => rfl
  | succ n h =>
    specialize h s.tail
    assumption

def stream.range (n: Nat) : stream Nat :=
  corec (λ x => (x, x+1)) n

@[simp] def stream.head_range (n: Nat) :
  head (range n) = n := by rfl

@[simp] def stream.tail_range (n: Nat) :
  tail (range n) = range (n+1) := by rfl

@[simp] def stream.get_range (n m: Nat) :
  (range n)[m] = n + m := by
  induction m generalizing n with
  | zero =>
    rfl
  | succ m h₁ =>
    simp only [get_succ, tail_range, h₁ (n+1)]
    simp_arith


def stream.duplicate : stream α → stream (stream α) :=
  corec (λ s => (s, s.tail))

@[simp] def stream.head_duplicate (s: stream α) :
  s.duplicate.head = s := by rfl

@[simp] def stream.tail_duplicate (s: stream α) :
  s.duplicate.tail = s.tail.duplicate := by rfl



def node.tenv := List Type

inductive node.state : node.tenv → Type 1 where
| Cons : {typ: Type} → {env: node.tenv} → typ → state env → state (typ :: env)
| Nil : state []


inductive node.eval : node.tenv → Type 1 where
| Cons : {typ: Type} → {env: node.tenv} → stream typ → eval env → eval (typ :: env)
| Nil : eval []

def node.eval.tail {env: node.tenv} : eval env → eval env
| Cons s tl => Cons s.tail tl
| Nil => Nil

def node.eval.get_state {env: node.tenv}: eval env → state env
| Cons s tl => state.Cons s.head (get_state tl)
| Nil => state.Nil

def node.equation (env: node.tenv) := eval env → Prop

def node.invariant (env: node.tenv) := state env → Prop

-- def node.indution (env: node.tenv) (eqs: equation env) (inv: invariant env) :
--   (∀ e: eval env, eqs e → inv e.get_state → inv e.tail.get_state) →
--   ∀ e:eval env, eqs e → inv e.get_state → (forall_inv inv e)
--   := by sorry

def node.tenv.test : tenv := [Nat, Nat, Bool]

def node.eval.test : node.eval node.tenv.test :=
  Cons (stream.const 1) (Cons (stream.const 2) (Cons (stream.const false) Nil))

def stream.forallSF (P: α → Prop) : (stream α → Prop) →o (stream α → Prop) where
  toFun aux s := P s.head ∧ aux s.tail
  monotone' := by
    intro a b h₁ x ⟨h₂, h₃⟩
    constructor
    . assumption
    . apply h₁
      assumption

instance {P: α → Prop} : ScottContinuousNat (stream.forallSF P) where
  scottContinuousNat := by
    intro S s h₁
    simp only [infᵢ_apply, infᵢ_Prop_eq] at h₁
    simp only [stream.forallSF] at *
    constructor
    . apply (h₁ 0).1
    . simp only [infᵢ_apply, infᵢ_Prop_eq]
      intro i
      apply (h₁ i).2

def stream.forallS (P: α → Prop) : stream α → Prop := gfp.scott (forallSF P)

def stream.forallS.unfold {P: α → Prop} {s: stream α} :
  forallS P s = (P s.head ∧ forallS P s.tail) := by
  conv =>
    lhs
    rw [forallS, ←gfp.scott.unfold]
    rfl


def stream.forallS.approx (P: α → Prop) : Nat → stream α → Prop
| n+1, s => P s.head ∧ approx P n s.tail
| 0, _ => True

#check gfp.approx
#print gfp.scott

def stream.forallS.rewrite_aux (P: α → Prop) (n: Nat) (s: stream α) :
  gfp.approx (forallSF P) n ⊤ s = approx P n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n h₁ =>
    specialize h₁ s.tail
    rw [approx, ←h₁]
    rfl

def stream.forallS.rewrite (P:α → Prop) (s: stream α) :
  forallS P s = (∀ n:Nat, approx P n s) := by
  simp only [forallS, infᵢ_apply, infᵢ_Prop_eq, gfp.scott]
  conv =>
    rhs
    intro n
    rw [←rewrite_aux P n s]
    rfl


#check congrArg
#check infᵢ_apply
#check infᵢ_Prop_eq

example : ∀ s₁: stream Nat,
  s₁ = (stream.const 1).fby s₁ → stream.forallS (λ x => 1 ≤ x) s₁ := by

  intro s₁ h₁
  simp? [stream.forallS, gfp.scott]
  intro n

  induction n generalizing s₁ with
  | zero =>
    trivial
  | succ n h₃ =>
    simp? [gfp.approx]
    apply And.intro
    . rw [h₁]
      simp? -- we can't `simp [h₁]` because of the recursive definition of `s₁`
    . apply h₃ s₁.tail
      . rw [h₁]
        simp only [stream.fby, stream.head_cons, stream.tail_cons]
        exact h₁


example : ∀ init, ∀ s₁ s₂: stream Nat,
  s₁ = (stream.const (init+1)).fby s₂ → s₂ = s₁ + stream.const 1 → stream.forallS (λ x => 1 ≤ x) s₁ := by

  intro init s₁ s₂ h₁ h₂
  simp? [stream.forallS, gfp.scott]
  intro n

  induction n generalizing init s₁ s₂ with
  | zero =>
    trivial
  | succ n h₃ =>
    simp? [gfp.approx]
    apply And.intro
    . rw [h₁]
      simp? -- we can't `simp [h₁]` because of the recursive definition of `s₁`
    . apply h₃ (init+1) s₁.tail s₂.tail
      <;> sorry



abbrev stream.TProp (α: Type u) := stream α → Prop

namespace stream.TProp

def square (p: TProp α) : TProp α := λ s => forallS p s.duplicate

inductive diamond (P: stream α → Prop) : TProp α where
| cons : ∀ s:stream α, diamond P s.tail → diamond P s
| nil : ∀ s:stream α, P s → diamond P s

inductive Until (P Q: stream α → Prop) : TProp α where
| cons : ∀ s: stream α, P s → Until P Q s.tail → Until P Q s
| nil : ∀ s: stream α, Q s → Until P Q s

def next (p: TProp α) : TProp α := λ s => p s.tail

def hd (p: TProp α) : TProp α := λ s => p (const s.head)

def pure (p: α → Prop) : TProp α := λ s => p s.head

def arrow (p q: TProp α) : TProp α := λ s => p s → q s

def not (p: TProp α) : TProp α := λ s => ¬p s

def diamond.unfold (p: TProp α) (s: stream α) :
  diamond p s = (p s ∨ next (diamond p) s) := by
  apply propext
  constructor
  . intro h₁
    cases h₁ with
    | cons _ h₁ =>
      apply Or.inr
      exact h₁
    | nil _ h₁ =>
      apply Or.inl
      exact h₁
  . intro h₁
    apply Or.elim h₁ <;> intro h₂
    . apply diamond.nil
      assumption
    . apply diamond.cons
      exact h₂

def square.unfold (p: TProp α) (s: stream α) :
  square p s = (p s ∧ next (square p) s) := by
  conv =>
    lhs
    rw [square, forallS, ←gfp.scott.unfold]
    rfl

def diamond.induction (p: TProp α) (s: stream α) :
  square (arrow p.next p) s → diamond p s → p s := by
  intro h₁ h₂
  induction h₂ with
  | nil s h₂ =>
    exact h₂
  | cons s _ h₃ =>
    rw [square.unfold, arrow, next, next] at h₁
    apply h₁.left
    apply h₃
    apply h₁.right


#print gfp.scott
#check infᵢ_apply
#check infᵢ_Prop_eq

def square.induction (p: TProp α) (s: stream α) :
  square (arrow p p.next) s → p s → square p s := by
  intro h₁ h₂
  rw [square, forallS.rewrite]
  rw [square, forallS.rewrite] at h₁
  intro n
  induction n generalizing s with
  | zero => trivial
  | succ n h₃ =>
    constructor
    . apply h₂
    . rw [tail_duplicate]
      apply h₃
      . intro n
        specialize h₁ (n+1)
        exact h₁.right
      . specialize h₁ 1
        simp only [forallS.approx, next, arrow, head_duplicate, and_true] at h₁
        apply h₁
        apply h₂

def not.self_dual (p: TProp α) : p.not.next = p.next.not := by
  rfl

def not.distributivity_arrow (p q: TProp α) : (arrow p q).next = arrow p.next q.next := by
  rfl

def not.distributivity_until (p q: TProp α) : (Until p q).next = Until p.next q.next := by
  funext s
  apply propext
  constructor <;> intro h₁
  . rw [next] at h₁
    generalize h₂: tail s = s' at *
    induction h₁ generalizing s with
    | nil s'' h₁ =>
      induction h₂
      apply Until.nil
      exact h₁
    | cons s'' h₁ h₃ h₄ =>
      induction h₂
      specialize h₄ (tail s) (Eq.refl _)
      apply Until.cons
      . apply h₁
      . apply h₄
  . induction h₁ with
    | nil s' h₁ =>
      apply Until.nil
      apply h₁
    | cons s' h₁ h₂ h₃ =>
      rw [next]
      apply Until.cons
      . apply h₁
      . apply h₃

theorem Until.unfold (p q: TProp α) (s: stream α) :
  Until p q s = (q s ∨ (p s ∧ next (Until p q) s)) := by
  apply propext
  constructor
  <;> intro h₁
  <;> cases h₁
  case a.mp.cons h₁ h₂ =>
    exact Or.inr (And.intro h₁ h₂)
  case a.mp.nil h₁ =>
    exact Or.inl h₁
  case a.mpr.inl h₁ =>
    exact Until.nil s h₁
  case a.mpr.inr h₁ =>
    exact Until.cons s h₁.left h₁.right

def bot : TProp α := λ _ => False
def top : TProp α := λ _ => True

@[simp] theorem Until.false (p: TProp α) : Until p bot = bot := by
  funext s
  apply propext
  constructor
  . intro h
    induction h with
    | nil _ h => exact h
    | cons _ _ _ h =>
      apply h
  . intro h
    apply False.elim
    apply h

theorem diamond.from_until (p: TProp α)  : diamond p = Until top p := by
  funext s
  apply propext
  constructor <;> intro h₁
  . induction h₁ with
    | nil s h₁ =>
      apply Until.nil _ h₁
    | cons s _ h₂ =>
      apply Until.cons
      . trivial
      . apply h₂
  . induction h₁ with
    | nil s h₁ =>
      apply diamond.nil _ h₁
    | cons s _ _ h₃ =>
      apply diamond.cons
      apply h₃





end TProp

-- Rec I tenv α represent a definition of a stream that
-- take set of streams of the form `∀ i: I, stream (tenv i)`
-- and construct a new stream of type `stream α`
inductive Rec (I: Type) (tenv: I → Type) : Type → Type 1 where
| tup {α β: Type} : Rec I tenv α → Rec I tenv β → Rec I tenv (α × β)
| fst {α β: Type} : Rec I tenv (α × β) → Rec I tenv α
| snd {α β: Type} : Rec I tenv (α × β) → Rec I tenv β
| map {α β: Type} : (α → β) → Rec I tenv α → Rec I tenv β
| fby {α: Type} : α → Rec I tenv α → Rec I tenv α
| ret {α: Type} : stream α → Rec I tenv α
| arg : (i: I) → Rec I tenv (tenv i)






instance Rec.instFunctor {I: Type} {tenv: I → Type} : Functor (stream.Rec I tenv) where
  map := .map

def Rec.ite {I α: Type} {tenv: I → Type}
  (i: Rec I tenv Bool) (t: Rec I tenv α) (e: Rec I tenv α) : Rec I tenv α :=
  (λ ⟨i, t, e⟩ => if i then t else e) <$> (.tup i (.tup t e))

-- evaluate a recursive equation over streams
def Rec.eval {I α: Type} {tenv: I → Type} (env: ∀ i: I, stream (tenv i)) : Rec I tenv α → stream α
| .tup lhs rhs => mkPair (eval env lhs) (eval env rhs)
| .fst pair => (eval env pair).fst
| .snd pair => (eval env pair).snd
| .fby x xs => cons x (eval env xs)
| .map f xs => f <$> (eval env xs)
| .arg i => env i
| .ret val => val

section Example
namespace stream

inductive I where
| x | y | z | t

abbrev tenv : I → Type
| .x => Nat
| .y => Bool
| .z => Nat
| .t => Prop

abbrev node : (i: I) → Rec I tenv (tenv i)
| .x => .fby 1 <| .ite (.arg I.y) (.arg I.z) ((· + 1) <$> .arg I.x)
| .y => .fby true ((·=false) <$> .arg I.y)
| .z => .ret (stream.cons 2 <| stream.const 1)
| .t => .fby True <| .arg I.t

abbrev property : (i: I) → tenv i → Prop
| .x, x => 1 ≤ x
| .y, _ => True
| .z, z => 1 ≤ z
| .t, t => t

abbrev property.check (env: ∀ i, stream <| tenv i) (h₁: ∀ i, forallS (property i) (env i))
  : (i: I) → forallS (property i) (Rec.eval env (node i))
| .x => by
  --rw [node, Rec.ite, Rec.instFunctor, Rec.eval]
  --simp only [Rec.eval]
  sorry
| .y => by
  specialize h₁ I.y
  rw [forallS.unfold]
  simp only [property, node, Rec.eval, true_and, tail_cons, Rec.instFunctor]
  sorry


| .z => by
  sorry
| .t => by
  --rw [forallS.unfold, property]
  --constructor
  --. apply True.intro
  --. specialize h₁ I.t
  --  rw [node]
  --  simp [Rec.eval]
  --  apply h₁
  sorry



end stream
end Example




