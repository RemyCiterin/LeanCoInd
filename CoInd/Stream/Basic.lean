import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils
import CoInd.Stream.LTLBase
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

@[simp] def stream.head_dulicate (s: stream α) :
  s.duplicate.head = s := by rfl

@[simp] def stream.tail_duplicate (s: stream α) :
  s.duplicate.tail = s.tail.duplicate := by rfl

abbrev TProp := stream Prop

namespace TProp

inductive UntilFn : TProp × TProp → Prop where
| Cons : ∀ {P Q}, P.head → UntilFn (P.tail, Q.tail) → UntilFn (P, Q)
| Nil : ∀ {P Q}, Q.head → UntilFn (P, Q)


instance : LTLBase TProp where
  Entails P Q := ∀ i:Nat, P[i] → Q[i]

  And P Q := (λ (x,y) => x ∧ y) <$> P.mkPair Q
  Imp P Q := (λ (x,y) => x → y) <$> P.mkPair Q
  Or  P Q := (λ (x,y) => x ∨ y) <$> P.mkPair Q

  Pure := stream.const

  Next := stream.tail

  Until P Q := UntilFn <$> P.duplicate.mkPair Q.duplicate

instance : LTL TProp where
  entails_reflexive := λ _ _ h => h
  entails_transitive := by
    intro P Q R h₁ h₂ i h₃
    apply h₂
    apply h₁
    apply h₃

  bientails_iff_eq := by
    intro P Q
    constructor
    . intro h₁
      apply stream.bisim (λ P Q => P ⊣⊢ Q)
      . intro P Q ⟨h₁, h₂⟩
        constructor
        . apply propext
          constructor
          . exact h₁ 0
          . exact h₂ 0
        . constructor
          <;> intro i
          . specialize h₁ (i+1)
            apply h₁
          . specialize h₂ (i+1)
            apply h₂
      assumption
    intro h
    induction h
    constructor <;> intro _ h' <;> exact h'

  and_elim_l := by
    intro P Q i h₁
    simp only [LTLBase.And, stream.get_map, stream.get_mkPair] at h₁
    exact h₁.left

  and_elim_r := by
    intro P Q i h₁
    simp only [LTLBase.And, stream.get_map, stream.get_mkPair] at h₁
    exact h₁.right

  and_intro := by
    intro P Q R h₁ h₂ i h₃
    simp only [LTLBase.And, stream.get_map, stream.get_mkPair]
    specialize h₁ i h₃
    specialize h₂ i h₃
    constructor <;> assumption

  or_intro_l := by
    intro P Q i h₁
    simp only [LTLBase.Or, stream.get_map, stream.get_mkPair]
    exact Or.inl h₁

  or_intro_r := by
    intro P Q i h₁
    simp only [LTLBase.Or, stream.get_map, stream.get_mkPair]
    exact Or.inr h₁

  or_elim := by
    intro P Q R h₁ h₂ i h₃
    simp only [LTLBase.Or, stream.get_map, stream.get_mkPair] at h₃
    cases h₃
    case inl h₄ =>
      exact h₁ i h₄
    case inr h₄ =>
      exact h₂ i h₄

  imp_intro := by
    intro P Q R h₁ i h₂
    simp only [LTLBase.Imp, stream.get_map, stream.get_mkPair]
    intro h₃
    apply h₁
    simp only [LTLBase.And, stream.get_map, stream.get_mkPair]
    constructor <;> assumption

  imp_elim := by
    intro P Q E h₁ i
    specialize h₁ i
    simp only [LTLBase.And, stream.get_map, stream.get_mkPair]
    simp only [LTLBase.Imp, stream.get_map, stream.get_mkPair] at h₁
    intro ⟨h₂, h₃⟩
    apply h₁ <;>
    assumption

  pure_intro := by
    intro ψ P h₁ i
    simp only [LTLBase.Pure, stream.get_const]
    intro _
    assumption

  pure_elim' := by
    intro ψ P h₁ i h₂
    simp only [LTLBase.Pure, stream.get_const] at h₂
    specialize h₁ h₂ i
    simp only [LTLBase.Pure, stream.get_const] at h₁
    apply h₁
    trivial







end TProp



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
