import CoInd.M
import CoInd.Paco
import CoInd.Tactic
import CoInd.Container
import CoInd.Utils
import Mathlib.Tactic.Eqns
import CoInd.Std.DelabRule
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.OmegaCompletePartialOrder
import CoInd.OmegaCompletePartialOrder
import CoInd.Notation
import CoInd.Kahn

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Monotonicity.Basic

import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq

#print OmegaCompletePartialOrder


open OmegaCompletePartialOrder

universe u v w u₀ u₁ u₂

variable {α : Type u}


inductive stream.A (α: Type u) where
| cons : α → stream.A α

def stream.B {α: Type u} : stream.A α → Type u
| .cons _ => PUnit

def stream.C (α: Type u) : Container := ⟨A α, stream.B⟩

inductive stream.F (α: Type u) (β: Type v) where
| cons : α → β → F α β

def stream (α: Type u) : Type u := Container.M (stream.C α)

#print stream.C
#print stream.A
#print stream.F

#check Container.Obj

def stream.corec.automaton
  {β: Type v} (f: β → F α β) (x: β) : Container.Obj (stream.C α) β :=
  match f x with
  | .cons a b => ⟨stream.A.cons a, λ _ => b⟩

def stream.corec {β: Type v} (f: β → F α β) (x₀: β) : stream α :=
  Container.M.corec (corec.automaton f) x₀

def stream.dest (k: stream α) : stream.F α (stream α) :=
  match Container.M.destruct k with
  | ⟨.cons x, f⟩ => .cons x (f PUnit.unit)

@[simp] theorem stream.dest_corec {β: Type v} (f: β → F α β) (x₀: β) :
  dest (corec f x₀) =
    match f x₀ with
    | .cons x xs => .cons x (corec f xs) := by
  rw [corec]
  simp [corec.automaton, dest, Container.M.destruct_corec]
  match f x₀ with
  | .cons x xs =>
    rfl


def stream.F.mk (k: F α (stream α)) : stream α :=
  match k with
  | .cons x xs =>
    Container.M.construct ⟨stream.A.cons x, λ _ => xs⟩

@[simp] def stream.dest_mk (k:F α (stream α)) : k.mk.dest = k := by
  match k with
  | .cons _ xs =>
    rfl

def stream.F.mk.inj (k k': F α (stream α)) :
  k.mk = k'.mk → k = k' := by
  intro h
  have h := congrArg dest h
  rw [dest_mk, dest_mk] at h
  assumption

@[simp] def stream.F.mk.injEq (k k': F α (stream α)) :
  (k.mk = k'.mk) = (k = k') := by
  apply propext
  constructor
  · apply inj
  · apply congrArg

instance : Cons α (stream α) where
  cons x xs := (stream.F.cons x xs).mk


@[elab_as_elim, cases_eliminator]
protected def stream.cases {motive: stream α → Sort w} (x: stream α)
  (cons: ∀ a (y: stream α), motive (a ::: y))
  : motive x :=
  Container.M.cases (λ ⟨node, children⟩ =>
    match node with
    | .cons x => cons x (children .unit)
  ) x


@[simp]
protected def stream.cases_cons {motive: stream α → Sort w} (a: α) (x: stream α)
  (cons: ∀ a x, motive (a ::: x)) :
  stream.cases (a ::: x) cons = cons a x := by
  rw [stream.cases]
  simp [F.mk, Cons.cons]

inductive stream.eqF (r : stream α → stream α → Prop) :
  stream α → stream α → Prop where
| cons {a b} (x : α) (xs ys: stream α) :
  x ::: xs = a → x ::: ys = b → r xs ys → eqF r a b

theorem stream.bisim (r : stream α → stream α → Prop)
  (hyp: ∀ s₁ s₂, r s₁ s₂ → eqF r s₁ s₂) : ∀ x y, r x y → x = y := by
  apply Container.M.bisim
  intro x y h₁
  specialize hyp _ _ h₁
  cases hyp with
  | cons head xs ys h₁ h₂ h₃ =>
    exists (.cons head)
    exists fun _ => xs
    exists fun _ => ys
    cases h₁
    cases h₂
    constructor
    · rfl
    · constructor
      · rfl
      · intro _
        apply h₃

def stream.dest.inj (k k': stream α) :
  k.dest = k'.dest → k = k' := by
  intro h
  apply bisim (λ k k' => k.dest = k'.dest) _ _ _ h
  intro s₁ s₂ h₁
  cases s₁ using stream.cases with
  | cons x xs =>
    cases s₂ using stream.cases with
    | cons y ys =>
      simp only [stream.dest_mk, Cons.cons, stream.F.cons.injEq] at h₁
      induction h₁.left
      induction h₁.right
      apply eqF.cons x xs xs
      · rfl
      · rfl
      · rfl

@[simp] def stream.dest.injEq (k k': stream α) :
  (k.dest = k'.dest) = (k = k') := by
  apply propext
  constructor
  · apply inj
  · apply congrArg


@[simp] def stream.mk_dest (k:stream α) : k.dest.mk = k := by
  apply dest.inj
  simp only [dest_mk]

def stream.cons.inj (x y: α) (xs ys: stream α) :
  x ::: xs = y ::: ys → x = y ∧ xs = ys := by
  intro h
  simp only [Cons.cons, F.mk.injEq, F.cons.injEq] at h
  assumption

def stream.cons.injEq (x y: α) (xs ys: stream α) :
  (x ::: xs = y ::: ys) = (x = y ∧ xs = ys) := by
  apply propext
  constructor
  · apply inj
  · intro h
    induction h.left
    induction h.right
    rfl


theorem stream.corec.unfold {β: Type v} (f: β → F α β) (x₀: β) :
  corec f x₀ =
      match f x₀ with
      | .cons x xs => x ::: (corec f xs) := by
  have := congrArg stream.F.mk (dest_corec f x₀)
  rw [mk_dest] at this
  rw [this]
  cases f x₀ with
  | cons x xs =>
    rfl

def stream.fst {α: Type u} {β: Type v} (k: stream (α × β)) : stream α :=
  corec
    (fun k => stream.cases k (cons:= λ x xs => F.cons x.fst xs)) k

def stream.snd {α: Type u} {β: Type v} (k: stream (α × β)) : stream β :=
  corec
    (fun k => stream.cases k (cons:= λ x xs => F.cons x.snd xs)) k

@[simp] theorem stream.fst.unfold
  {α: Type u} {β: Type v} (x: α × β) (xs : stream (α × β)) :
  @stream.fst α β (x ::: xs) = x.fst ::: xs.fst := by
  rw [fst, corec.unfold, stream.cases_cons, cons.injEq]
  trivial


@[simp] theorem stream.snd.unfold
  {α: Type u} {β: Type v} (x: α × β) (xs : stream (α × β)) :
  @stream.snd α β (x ::: xs) = x.snd ::: xs.snd := by
  rw [snd, corec.unfold, stream.cases_cons, cons.injEq]
  trivial


def stream.tup {α: Type u} {β: Type v}
  (k₁: stream α) (k₂: stream β) : stream (α × β) :=
  corec (fun (x, y) =>
    match dest x, dest y with
    | .cons x xs, .cons y ys => .cons (x, y) (xs, ys)
  ) (k₁, k₂)


@[simp] theorem stream.tup.unfold
  {α: Type u} {β: Type v} (x: α) (xs: stream α) (y: β) (ys: stream β) :
  @tup α β (x ::: xs) (y ::: ys) = (x, y) ::: tup xs ys := by
  rw [tup, corec.unfold]
  have h₁ : dest (x ::: xs) = .cons x xs := by rfl
  have h₂ : dest (y ::: ys) = .cons y ys := by rfl
  simp only [h₁, h₂]
  rfl

--attribute [eqns stream.tup.unfold stream.tup.unfold_bot_left stream.tup.unfold_bot_right] stream.tup

@[simp] theorem stream.tup_fst_snd
  {α: Type u} {β: Type v} (k: stream (α × β)) :
  tup k.fst k.snd = k := by
  coinduction generalizing [k] using bisim
  intro s₁ s₂ ⟨x, h₁, h₂, _⟩
  induction h₁
  cases x with
  | cons x xs =>
    simp only
      [fst.unfold, snd.unfold, tup.unfold, Prod.mk.eta] at h₂
    induction h₂
    apply eqF.cons x (tup xs.fst xs.snd) xs rfl rfl
    exists xs


def stream.fby (x y: stream α) : stream α :=
  stream.cases x (cons := λ x _ => x ::: y)

@[simp] def stream.fby.unfold (x : α) (xs y: stream α) :
  fby (x ::: xs) y = x ::: y := by
  rw [fby, stream.cases_cons]

--attribute [eqns stream.fby.unfold_bot stream.fby.unfold] stream.fby


def stream.map {α: Type u} {β: Type v} (f: α → β) (x: stream α) : stream β :=
  stream.corec (λ x =>
      stream.cases x (cons := λ x xs =>
        .cons (f x) xs
      )
    ) x


@[simp] def stream.map.unfold
  {α: Type u} {β: Type v} (f: α → β) (x: α) (xs: stream α) :
  map f (x ::: xs) = f x ::: map f xs := by
  rw [map, corec.unfold, stream.cases_cons]
  rfl


def stream.const (x: α) : stream α :=
  corec (λ _ => .cons x Unit.unit) Unit.unit

def stream.const.unfold (x: α) : const x = (x ::: const x) := by
  conv =>
    lhs
    simp only [const]
    rw [corec.unfold]
    rfl
  rfl

-- Addition of streams
instance {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ] :
  HAdd (stream α) (stream β) (stream γ) where
  hAdd k₁ k₂ := stream.map (Function.uncurry HAdd.hAdd) (stream.tup k₁ k₂)


@[simp] def stream.add.unfold
  {α: Type u} {β: Type v} {γ: Type w} [HAdd α β γ]
  (x: α) (xs: stream α) (y: β) (ys: stream β) :
  (x ::: xs) + (y ::: ys) = (x + y) ::: (xs + ys) := by simp [HAdd.hAdd]



-- Substraction of streams
instance {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ] :
  HSub (stream α) (stream β) (stream γ) where
  hSub k₁ k₂ := stream.map (Function.uncurry HSub.hSub) (stream.tup k₁ k₂)

@[simp] def stream.sub.unfold
  {α: Type u} {β: Type v} {γ: Type w} [HSub α β γ]
  (x: α) (xs: stream α) (y: β) (ys: stream β) :
  (x ::: xs) - (y ::: ys) = (x - y) ::: (xs - ys) := by simp [HSub.hSub]


-- Multiplication of streams
instance {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ] :
  HMul (stream α) (stream β) (stream γ) where
  hMul k₁ k₂ := stream.map (Function.uncurry HMul.hMul) (stream.tup k₁ k₂)

@[simp] def stream.mul.unfold
  {α: Type u} {β: Type v} {γ: Type w} [HMul α β γ]
  (x: α) (xs: stream α) (y: β) (ys: stream β) :
  (x ::: xs) * (y ::: ys) = (x * y) ::: (xs * ys) := by simp [HMul.hMul]


-- Division of streams
instance {α: Type u} {β: Type v} {γ: Type w} [HDiv α β γ] :
  HDiv (stream α) (stream β) (stream γ) where
  hDiv k₁ k₂ := stream.map (Function.uncurry HDiv.hDiv) (stream.tup k₁ k₂)

@[simp] def stream.div.unfold
  {α: Type u} {β: Type v} {γ: Type w}
  [HDiv α β γ] (x: α) (xs: stream α) (y: β) (ys: stream β) :
  (x ::: xs) / (y ::: ys) = (x / y) ::: (xs / ys) := by simp [HDiv.hDiv]



-- Modular arithmetic over streams
instance {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ] :
  HMod (stream α) (stream β) (stream γ) where
  hMod k₁ k₂ := stream.map (Function.uncurry HMod.hMod) (stream.tup k₁ k₂)


@[simp] def stream.mod.unfold
  {α: Type u} {β: Type v} {γ: Type w} [HMod α β γ]
  (x: α) (xs: stream α) (y: β) (ys: stream β) :
  (x ::: xs) % (y ::: ys) = (x % y) ::: (xs % ys) := by simp [HMod.hMod]


def stream.and : stream Prop → stream Prop → stream Prop := λ k₁ k₂ =>
  stream.map (Function.uncurry And) (stream.tup k₁ k₂)

@[simp] def stream.and.unfold
  (x: Prop) (xs: stream Prop) (y: Prop) (ys: stream Prop) :
  stream.and (x ::: xs) (y ::: ys) = (x ∧ y) ::: stream.and xs ys
  := by simp [stream.and]


def stream.not : stream Prop → stream Prop := λ k₁ =>
  stream.map Not k₁

@[simp] def stream.not.unfold (x: Prop) (xs: stream Prop) :
  stream.not (x ::: xs) = (¬x) ::: stream.not xs := by simp [stream.not]



def stream.or : stream Prop → stream Prop → stream Prop := λ k₁ k₂ =>
  stream.map (Function.uncurry Or) (stream.tup k₁ k₂)

@[simp] def stream.or.unfold
  (x: Prop) (xs: stream Prop) (y: Prop) (ys: stream Prop) :
  stream.or (x ::: xs) (y ::: ys) = (x ∨ y) ::: stream.or xs ys
  := by simp [stream.or]



def stream.eq : stream α → stream α → stream Prop := λ k₁ k₂ =>
  stream.map (Function.uncurry Eq) (stream.tup k₁ k₂)

@[simp] def stream.eq.unfold
  (x: α) (xs: stream α) (y: α) (ys: stream α) :
  stream.eq (x ::: xs) (y ::: ys) = (x = y) ::: stream.eq xs ys
  := by simp [stream.eq]





def stream.le [LE α] : stream α → stream α → stream Prop := λ k₁ k₂ =>
  stream.map (Function.uncurry LE.le) (stream.tup k₁ k₂)

@[simp] def stream.le.unfold [LE α]
  (x: α) (xs: stream α) (y: α) (ys: stream α) :
  stream.le (x ::: xs) (y ::: ys) = (x ≤ y) ::: stream.le xs ys
  := by simp [stream.le]

@[simp] def stream.ge [LE α] (x y: stream α) := stream.le y x


def stream.lt [LT α] : stream α → stream α → stream Prop := λ k₁ k₂ =>
  stream.map (Function.uncurry LT.lt) (stream.tup k₁ k₂)

@[simp] def stream.lt.unfold [LT α]
  (x: α) (xs: stream α) (y: α) (ys: stream α) :
  stream.lt (x ::: xs) (y ::: ys) = (x < y) ::: stream.lt xs ys
  := by simp [stream.lt]

@[simp] def stream.gt [LT α] (x y: stream α) := stream.lt y x

-- Defintion of mux (if then else operators) over streams
noncomputable def stream.mux (x: stream Prop) (y z: stream α) : stream α :=
  stream.map
    (λ ⟨a, b, c⟩ => @ite _ a (Classical.propDecidable a) b c)
    (stream.tup x (stream.tup y z))

@[simp] def stream.mux.unfold_true
  (y z: α) (xs: stream Prop) (ys zs: stream α) :
  stream.mux (True ::: xs) (y ::: ys) (z ::: zs) = y ::: (xs.mux ys zs) := by
  simp [stream.mux]

@[simp] def stream.mux.unfold_false
  (y z: α) (xs: stream Prop) (ys zs: stream α) :
  stream.mux (False ::: xs) (y ::: ys) (z ::: zs) = z ::: (xs.mux ys zs) := by
  simp [stream.mux]


def stream.next (x: stream α) : stream α :=
  stream.cases (cons := λ _ xs => xs) x

@[simp] def stream.next.unfold (x: α) (xs: stream α) :
  stream.next (x ::: xs) = xs := by
  rw [stream.next, stream.cases_cons]

def stream.tail (x: stream α) : stream α :=
  x.next

@[simp] def stream.tail.unfold (x: α) (xs: stream α) :
  stream.tail (x ::: xs) = xs := stream.next.unfold x xs

#check stream.F.mk.inj


def stream.head (x: stream α) : α :=
  stream.cases (cons := λ x _ => x) x

@[simp] def stream.head.unfold (x: α) (xs: stream α) :
  stream.head (x ::: xs) = x := by
  rw [stream.head, stream.cases_cons]



def stream.first (x: stream α) : stream α :=
  stream.const (x.head)

@[simp] def stream.first.unfold
  (x: α) (xs: stream α) : stream.first (x ::: xs) = const x := by
  rw [stream.first, stream.head, stream.cases_cons]






-- Now we want to use streams to define LTL properties

inductive stream.EntailsF (aux: stream Prop → Prop) : stream Prop → Prop where
| cons {s} (p: Prop) (ps: stream Prop) :
  p → aux ps → p ::: ps = s → EntailsF aux s

def stream.EntailsF.mono : Monotone stream.EntailsF := by
  intro r₁ r₂ h₁ s h₂
  cases h₂ with
  | cons p ps h₂ h₃ h₄ =>
    exact EntailsF.cons p ps h₂ (h₁ _ h₃) h₄

def stream.Entails := pgfp ⟨EntailsF, EntailsF.mono⟩ ⊥

#check pgfp.unfold
#check stream.cons.inj

def stream.Entails.unfold (x: Prop) (xs: stream Prop) :
  Entails (x ::: xs) = (x ∧ Entails xs) := by
  apply propext
  conv =>
    lhs
    rw [Entails, ←pgfp.unfold]
    simp
  constructor
  · intro h₁
    cases h₁ with
    | cons p ps h₁ h₂ h₃ =>
      have ⟨h₄, h₅⟩ := stream.cons.inj _ _ _ _ h₃
      induction h₄
      induction h₅
      constructor
      · exact h₁
      · exact h₂
  · intro ⟨h₁, h₂⟩
    apply EntailsF.cons x xs h₁ h₂ rfl

#check pgfp.coinduction
#check pgfp.accumulate

def stream.Entails.coind
  (hyp: stream Prop → Prop)
  (h₁: ∀ x, hyp x → x.head ∧ hyp x.tail)
  (s: stream Prop) (h₂: hyp s) : Entails s := by
  have := (pgfp.coinduction ⟨EntailsF, EntailsF.mono⟩ hyp).2
  apply this
  clear this
  · intro s
    cases s with
    | cons x xs =>
      intro h₃
      apply EntailsF.cons x xs (h₁ (x ::: xs) h₃).1
      · apply Or.inl
        apply (h₁ (x ::: xs) h₃).right
      · rfl
  · assumption




-- A projection from Kahn networks to streams using a default value in case of
-- we see ⊥
def ωStream.proj (s: ωStream α) (default: α) : stream α :=
  stream.corec
    (λ s =>
      ωStream.cases
        (bot := stream.F.cons default ⊥)
        (cons := λ x xs => stream.F.cons x xs)
        s
    ) s

@[simp] def ωStream.proj.unfold_bot (default: α) :
  (⊥: ωStream α).proj default = stream.const default := by
  coinduction generalizing [] using stream.bisim
  intro s₁ s₂ ⟨eq₁, eq₂, _⟩
  induction eq₁
  induction eq₂
  apply stream.eqF.cons default
    ((⊥: ωStream α).proj default) (stream.const default)
  · conv =>
      rhs
      simp [proj]
      rw [stream.corec.unfold]
      simp
    rfl
  · simp [←stream.const.unfold]
  · simp


@[simp] def ωStream.proj.unfold_cons (x: α) (xs: ωStream α) (default: α) :
  (x ::: xs).proj default = x ::: xs.proj default := by
  rw [proj, stream.corec.unfold]
  rfl


-- An injective function from infinite streams to finite or infinite streams
def stream.inj (s: stream α) : ωStream α :=
  ωStream.corec (λ s => stream.cases (cons := λ x xs => .cons x xs) s) s

@[simp] def stream.inj.unfold (x: α) (xs: stream α) :
  (x ::: xs).inj = x ::: xs.inj := by
  rw [inj, ωStream.corec.unfold]
  rfl

@[simp] def stream.inj.injEq (x y: stream α) :
  (inj x = inj y) = (x = y) := by
  apply propext
  constructor
  · intro h
    coinduction generalizing [x, y] using stream.bisim
    clear x y
    intro l r ⟨x, y, eq₁, eq₂, h₁⟩
    induction eq₁
    induction eq₂
    cases x
    cases y
    case cons x xs y ys =>
      simp at h₁
      rw [ωStream.cons.injEq] at h₁
      induction h₁.left
      apply eqF.cons x xs ys rfl rfl
      exists xs
      exists ys
      simp [h₁.right]
  · intro h
    rw [h]
