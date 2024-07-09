import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils


import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq

universe u v w u₀ u₁ u₂

variable {α: Type u}

#print Container
#print Container.Obj

def streamC (α: Type u) : Container := ⟨α, fun _ => PUnit⟩

def stream (α: Type u) := Container.M (streamC α)

def stream.head (s: stream α) : α := s.destruct.fst

def stream.tail (s: stream α) : stream α := s.destruct.snd PUnit.unit

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

@[simp] def stream.fby (s₁ s₂: stream α) : stream α :=
  cons (head s₁) s₂

#check Container.M.corec
def stream.const (x: α) : stream α := Container.M.corec (fun u => ⟨x, fun _ => u⟩) Unit.unit

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

def stream.lift (s₁: stream α) (f: α → β) : stream β :=
  Container.M.corec (λ s => ⟨f s.head, λ _ => s.tail⟩) s₁

@[simp] def stream.head_lift (f: α → β) :
  ∀ s: stream α, (s.lift f).head = f s.head := by
  intro s
  simp only [lift, head]
  rw [Container.M.destruct_corec]
  simp only [Container.Map]

@[simp] def stream.tail_lift (f: α → β) :
  ∀ s: stream α, (s.lift f).tail = s.tail.lift f := by
  intro s
  simp only [lift, tail]
  rw [Container.M.destruct_corec]
  simp only [Container.Map]
  simp only [Function.comp_apply]

def stream.lift2 (s₁: stream α) (s₂: stream β) (f: α → β → γ) : stream γ :=
  Container.M.corec (λ (s₁, s₂) => ⟨f s₁.head s₂.head, λ _ => (s₁.tail, s₂.tail)⟩) (s₁, s₂)

@[simp] def stream.head_lift2 (f: α → β → γ) :
  ∀ (s₁: stream α) (s₂: stream β), (s₁.lift2 s₂ f).head = f s₁.head s₂.head := by
  intro s₁ s₂
  simp only [lift2, head]
  rw [Container.M.destruct_corec]
  simp only [Container.Map]

@[simp] def stream.tail_lift2 (f: α → β → γ) :
  ∀ (s₁: stream α) (s₂: stream β), (s₁.lift2 s₂ f).tail = s₁.tail.lift2 s₂.tail f := by
  intro s₁ s₂
  simp only [lift2, tail]
  rw [Container.M.destruct_corec]
  simp only [Container.Map]
  simp only [Function.comp_apply]

def stream.lift3 (s₁: stream α) (s₂: stream β) (s₃: stream γ) (f: α → β → γ → η) : stream η :=
  (s₁.lift2 s₂ Prod.mk).lift2 s₃ (λ (x₁, x₂) x₃ => f x₁ x₂ x₃)

@[simp] def stream.head_lift3 (f: α → β → γ → η) :
  ∀ (s₁: stream α) (s₂: stream β) (s₃: stream γ), (s₁.lift3 s₂ s₃ f).head = f s₁.head s₂.head s₃.head := by
  intro s₁ s₂ s₃
  simp only [lift3, head_lift2]

@[simp] def stream.tail_lift3 (f: α → β → γ → η) :
  ∀ (s₁: stream α) (s₂: stream β) (s₃: stream γ), (s₁.lift3 s₂ s₃ f).tail = s₁.tail.lift3 s₂.tail s₃.tail f := by
  intro s₁ s₂ s₃
  simp only [lift3, tail_lift2]



instance [HAdd α β γ] : HAdd (stream α) (stream β) (stream γ) where
  hAdd s₁ s₂ := s₁.lift2 s₂ HAdd.hAdd

instance [HSub α β γ] : HSub (stream α) (stream β) (stream γ) where
  hSub s₁ s₂ := s₁.lift2 s₂ HSub.hSub

instance [HMul α β γ] : HMul (stream α) (stream β) (stream γ) where
  hMul s₁ s₂ := s₁.lift2 s₂ HMul.hMul

instance [HDiv α β γ] : HDiv (stream α) (stream β) (stream γ) where
  hDiv s₁ s₂ := s₁.lift2 s₂ HDiv.hDiv

instance [HMod α β γ] : HMod (stream α) (stream β) (stream γ) where
  hMod s₁ s₂ := s₁.lift2 s₂ HMod.hMod

instance [HAnd α β γ] : HAnd (stream α) (stream β) (stream γ) where
  hAnd s₁ s₂ := s₁.lift2 s₂ HAnd.hAnd

instance [HOr α β γ] : HOr (stream α) (stream β) (stream γ) where
  hOr s₁ s₂ := s₁.lift2 s₂ HOr.hOr

instance [HXor α β γ] : HXor (stream α) (stream β) (stream γ) where
  hXor s₁ s₂ := s₁.lift2 s₂ HXor.hXor

@[simp] theorem stream.head_add [HAdd α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ + s₂) = s₁.head + s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_sub [HSub α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ - s₂) = s₁.head - s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_mul [HMul α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ * s₂) = s₁.head * s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_div [HDiv α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ / s₂) = s₁.head / s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_mod [HMod α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ % s₂) = s₁.head % s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_and [HAnd α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ &&& s₂) = s₁.head &&& s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_or  [HOr  α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ ||| s₂) = s₁.head ||| s₂.head := head_lift2 _ s₁ s₂
@[simp] theorem stream.head_xor [HXor α β γ] (s₁: stream α) (s₂:stream β) : head (s₁ ^^^ s₂) = s₁.head ^^^ s₂.head := head_lift2 _ s₁ s₂

@[simp] theorem stream.tail_add [HAdd α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ + s₂) = s₁.tail + s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_sub [HSub α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ - s₂) = s₁.tail - s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_mul [HMul α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ * s₂) = s₁.tail * s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_div [HDiv α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ / s₂) = s₁.tail / s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_mod [HMod α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ % s₂) = s₁.tail % s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_and [HAnd α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ &&& s₂) = s₁.tail &&& s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_or  [HOr  α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ ||| s₂) = s₁.tail ||| s₂.tail := tail_lift2 _ s₁ s₂
@[simp] theorem stream.tail_xor [HXor α β γ] (s₁: stream α) (s₂:stream β) : tail (s₁ ^^^ s₂) = s₁.tail ^^^ s₂.tail := tail_lift2 _ s₁ s₂


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


class LTLBase (PROP: Type u) where
  entails : PROP → PROP → Prop

  top : PROP
  bot : PROP

  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  impl : PROP → PROP → PROP
  Until : PROP → PROP → PROP
  Next : PROP → PROP

def LTLBase.not {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP := impl p bot
def LTLBase.iff {PROP: Type u} [LTLBase PROP] (p₁ p₂: PROP) : PROP := and (impl p₁ p₂) (impl p₂ p₁)
def LTLBase.diamond {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP := Until top p
def LTLBase.square {PROP: Type u} [LTLBase PROP] (p: PROP) : PROP := not (diamond (not p))


declare_syntax_cat LTL -- (behavior := symbol)

syntax:max " ∘ " LTL:40 : LTL -- next
syntax:max " □ " LTL:40 : LTL -- forall
syntax:max " ⋄ " LTL:40 : LTL -- exists
syntax:37 LTL:37 " ∪ " LTL:38 : LTL -- until

syntax:35 LTL:36 " ∧ " LTL:35 : LTL
syntax:30 LTL:31 " ∨ " LTL:30 : LTL
syntax:10 LTL:10 " → " LTL:11 : LTL
syntax:20 LTL:20 " ↔ " LTL:20 : LTL
syntax:max " ¬ " LTL:40 : LTL
syntax "⊤" : LTL
syntax "⊥" : LTL

syntax:max " ( " LTL " ) " : LTL

syntax ident : LTL
syntax num : LTL
syntax "[| " LTL "]" : term
syntax " { " term " } " : LTL
syntax term " ⊢ " term : term

#check Lean.RBMap
#print String.length
#print Ordering

def String.cmp : String → String → Ordering
| .mk lhs, .mk rhs =>
  let rec aux : List Char → List Char → Ordering
    | x :: xs, y :: ys =>
      if x < y then .lt else if y < x then .gt else aux xs ys
    | _ :: _, [] => .gt
    | [], _ :: _ => .lt
    | [], [] => .eq
  aux lhs rhs

#check Lean.RBMap.ofList

def LTL.UnopMap : Lean.RBMap String (Nat × Nat) String.cmp :=
  Lean.RBMap.ofList [
    ⟨"∘", 100, 40⟩,
    ⟨"□", 100, 40⟩,
    ⟨"⋄", 100, 40⟩,
    ⟨"¬", 100, 40⟩
  ]

def LTL.BinopMap : Lean.RBMap String (Nat × Nat × Nat) String.cmp :=
  Lean.RBMap.ofList [
    ⟨"∪", 37, 37, 38⟩,
    ⟨"∧", 35, 36, 35⟩,
    ⟨"∨", 30, 31, 30⟩,
    ⟨"→", 10, 11, 10⟩,
    ⟨"↔", 20, 21, 21⟩
  ]

open Lean PrettyPrinter Delaborator SubExpr Meta

partial def termAsLTL [Monad M] [MonadQuotation M] : TSyntax `term → M (TSyntax `LTL × Nat)
-- ****** Binop ******
| `(LTLBase.and $t₁ $t₂) => do
  let ⟨N, N₁, N₂⟩ := LTL.BinopMap.findD "∧" ⟨0, 100, 100⟩
  let (l₁, n₁) ← termAsLTL t₁
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  let (l₂, n₂) ← termAsLTL t₂
  let l₂ ← if n₂ < N₂ then `(LTL| ($l₂)) else pure l₂
  return (← `(LTL| $l₁ ∧ $l₂), N)
| `(LTLBase.or $t₁ $t₂) => do
  let ⟨N, N₁, N₂⟩ := LTL.BinopMap.findD "∨" ⟨0, 0, 0⟩
  let (l₁, n₁) ← termAsLTL t₁
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  let (l₂, n₂) ← termAsLTL t₂
  let l₂ ← if n₂ < N₂ then `(LTL| ($l₂)) else pure l₂
  return (← `(LTL| $l₁ ∨ $l₂), N)
| `(LTLBase.impl $t₁ $t₂) => do
  let ⟨N, N₁, N₂⟩ := LTL.BinopMap.findD "→" ⟨0, 0, 0⟩
  let (l₁, n₁) ← termAsLTL t₁
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  let (l₂, n₂) ← termAsLTL t₂
  let l₂ ← if n₂ < N₂ then `(LTL| ($l₂)) else pure l₂
  return (← `(LTL| $l₁ → $l₂), N)
| `(LTLBase.Until $t₁ $t₂) => do
  let ⟨N, N₁, N₂⟩ := LTL.BinopMap.findD "∪" ⟨0, 0, 0⟩
  let (l₁, n₁) ← termAsLTL t₁
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  let (l₂, n₂) ← termAsLTL t₂
  let l₂ ← if n₂ < N₂ then `(LTL| ($l₂)) else pure l₂
  return (← `(LTL| $l₁ ∪ $l₂), N)
| `(LTLBase.iff $t₁ $t₂) => do
  let ⟨N, N₁, N₂⟩ := LTL.BinopMap.findD "↔" ⟨0, 0, 0⟩
  let (l₁, n₁) ← termAsLTL t₁
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  let (l₂, n₂) ← termAsLTL t₂
  let l₂ ← if n₂ < N₂ then `(LTL| ($l₂)) else pure l₂
  return (← `(LTL| $l₁ ↔ $l₂), N)
-- ****** Unop ******
| `(LTLBase.diamond $t) => do
  let (N, N₁) := LTL.UnopMap.findD "⋄" ⟨0, 0⟩
  let (l₁, n₁) ← termAsLTL t
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  return (← `(LTL| ⋄$l₁), N)
| `(LTLBase.square $t) => do
  let (N, N₁) := LTL.UnopMap.findD "□" ⟨0, 0⟩
  let (l₁, n₁) ← termAsLTL t
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  return (← `(LTL| □$l₁), N)
| `(LTLBase.Next $t) => do
  let (N, N₁) := LTL.UnopMap.findD "∘" ⟨0, 0⟩
  let (l₁, n₁) ← termAsLTL t
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  return (← `(LTL| ∘$l₁), N)
| `(LTLBase.not $t) => do
  let (N, N₁) := LTL.UnopMap.findD "¬" ⟨0, 0⟩
  let (l₁, n₁) ← termAsLTL t
  let l₁ ← if n₁ < N₁ then `(LTL| ($l₁)) else pure l₁
  return (← `(LTL| ¬$l₁), N)
-- ****** Contants and antiquotation ******
| `([| $p:LTL ]) => return (← `(LTL| ($p)), 100)
| `(LTLBase.top) => return (← `(LTL| ⊤), 100)
| `(LTLBase.bot) => return (← `(LTL| ⊥), 100)
| `($t:ident) => do
  return (.mk t.1, 100)
| `($t:term) => return (← `(LTL| {$t}), 100)

@[app_unexpander LTLBase.entails]
def unexpandEntails : Unexpander
| `(term| LTLBase.entails $t₁:term $t₂:term) => do
  let l₁ ← termAsLTL t₁
  let l₂ ← termAsLTL t₂
  `([| $l₁.fst ] ⊢ [| $l₂.fst ])
| _ => throw ()

macro_rules
| `($t₁:term ⊢ $t₂:term) => `(LTLBase.entails $t₁ $t₂)
| `([| $t₁:LTL ∧ $t₂:LTL]) => `(LTLBase.and [|$t₁] [|$t₂])
| `([| $t₁:LTL ∨ $t₂:LTL]) => `(LTLBase.or [|$t₁] [|$t₂])
| `([| $t₁:LTL → $t₂:LTL]) => `(LTLBase.impl [|$t₁] [|$t₂])
| `([| $t₁:LTL ↔ $t₂:LTL]) => `(LTLBase.iff [|$t₁] [|$t₂])
| `([| $t₁:LTL ∪ $t₂:LTL]) => `(LTLBase.Until [|$t₁] [|$t₂])
| `([| □ $t₁:LTL]) => `(LTLBase.square [|$t₁])
| `([| ⋄ $t₁:LTL]) => `(LTLBase.diamond [|$t₁])
| `([| ¬ $t₁:LTL]) => `(LTLBase.not [|$t₁])
| `([| ∘ $t₁:LTL]) => `(LTLBase.Next [|$t₁])
| `([| ( $t₁:LTL ) ]) => `([|$t₁])
| `([| ⊤ ]) => `(LTLBase.top)
| `([| ⊥ ]) => `(LTLBase.bot)
| `([| { $t₁:term } ]) => `($t₁)
| `([| $i:ident ]) => `($i)

#check ∀ A B C D: Prop, (¬A) ∧ B ∧ (C → D)
#check ∀ (PROP: Type u) [LTLBase PROP] (A B C D: PROP), [| (¬(A ∪ B)) ∪ (C ∪ D) ] ⊢ [|(A ↔ B) ↔ (C ↔ D)]

#print Transitive
#print Reflexive

class LTL (PROP: Type u) [inst: LTLBase PROP] where
  bientails (P Q: PROP) := (P ⊢ Q) ∧ (Q ⊢ P)

  entails_transitive: Transitive inst.entails
  entails_reflexive: Reflexive inst.entails

  bientails_iff (P Q: PROP) : (bientails P Q) ↔ (P = Q)

  and_intro (P Q R: PROP) : (P ⊢ Q) → (P ⊢ R) → (P ⊢ [| Q ∧ R ])
