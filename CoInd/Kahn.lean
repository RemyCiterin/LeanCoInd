
import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils
import CoInd.Eqns
import CoInd.Std.DelabRule

import Mathlib.Tactic.Linarith


import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Qq

universe u v w u₀ u₁ u₂

variable {α : Type u}

#print Container
#print Container.Obj

inductive Kahn.A (α: Type u) where
| cons : α → Kahn.A α
| eps

def Kahn.C (α: Type u) : Container := ⟨A α, fun _ => PUnit⟩

inductive Kahn.F (α: Type u) (β: Type v) where
| cons : α → β → F α β
| eps : β → F α β

instance [Inhabited β] : Inhabited (Kahn.F α β) where
  default := .eps default

def Kahn (α: Type u) : Type u := Container.M (Kahn.C α)

#print Kahn.C
#print Kahn.A
#print Kahn.F

#check Container.Obj

def Kahn.corec.automaton {β: Type v} (f: β → F α β) (x: β) : Container.Obj (Kahn.C α) β :=
  match f x with
  | .eps b => { fst := Kahn.A.eps, snd := λ _ => b}
  | .cons a b => ⟨Kahn.A.cons a, λ _ => b⟩

def Kahn.corec {β: Type v} (f: β → F α β) (x₀: β) : Kahn α :=
  Container.M.corec (corec.automaton f) x₀

def Kahn.dest (k: Kahn α) : Kahn.F α (Kahn α) :=
  match Container.M.destruct k with
  | ⟨.cons x, f⟩ => .cons x (f PUnit.unit)
  | ⟨.eps, f⟩ => .eps (f PUnit.unit)

def Kahn.F.mk (k: F α (Kahn α)) : Kahn α :=
  match k with
  | .eps xs =>
    Container.M.construct ⟨Kahn.A.eps, λ _ => xs⟩
  | .cons x xs =>
    Container.M.construct ⟨Kahn.A.cons x, λ _ => xs⟩

@[simp] def Kahn.dest_mk (k:F α (Kahn α)) : k.mk.dest = k := by
  match k with
  | .eps xs =>
    rfl
  | .cons _ xs =>
    rfl

macro "eps(" t:term ")" : term => `(Kahn.F.mk (Kahn.F.eps $t))
macro "cons(" a:term "," t:term ")" : term => `(Kahn.F.mk (Kahn.F.cons $a $t))


delab_rule Kahn.F.mk
| `($_ (Kahn.F.cons $a $t)) => `(cons($a, $t))
| `($_ (Kahn.F.eps $t)) => `(eps($t))
| `($_ ($t)) => `(eps($t))

example (x: Kahn Nat) (y: Kahn.F Nat <| Kahn Nat) : y.mk ≠ (Kahn.F.eps x).mk := by
  intro h
  sorry

def Kahn.bot : Kahn α :=
  corec (λ _ => .eps .unit) Unit.unit

instance : Inhabited (Kahn α) where
  default := Kahn.bot

def Kahn.bot? (k: Kahn α) : Prop := k = bot

def Kahn.dest_bot : (@bot α).dest = F.eps bot := by rfl

instance : Nonempty (Kahn α) := ⟨Kahn.bot⟩

-- return if a kahn network is a cons
def Kahn.cons? (k: F α β) : Prop :=
  match k with
  | .cons _ _ => True
  | _ => False

instance Kahn.cons?.decide (k: F α β) : Decidable (cons? k) :=
  match k with
  | .cons _ _ => isTrue (by rw [cons?]; trivial)
  | .eps _ => isFalse (by rw [cons?]; intro h; apply False.elim h)

-- return if a kahn network is an epsilon
def Kahn.eps? (k: F α β) : Prop :=
  match k with
  | .eps _ => True
  | _ => False

instance Kahn.eps?.decide (k: F α β) : Decidable (eps? k) :=
  match k with
  | .cons _ _ => isFalse (by rw [eps?]; intro h; apply False.elim h)
  | .eps _ => isTrue (by rw [eps?]; trivial)

-- attribute [eqns Kahn.head_corec] Kahn.head

def Kahn.bisimF (r: Kahn α → Kahn α → Prop) (s₁ s₂: Kahn α) : Prop :=
  match s₁.dest, s₂.dest with
  | (.eps s₁'), (.eps s₂') =>
    r s₁' s₂'
  | (.cons x s₁'), (.cons y s₂') =>
    x = y ∧ r s₁' s₂'
  | _, _ => False

theorem Kahn.bisim (r: Kahn α → Kahn α → Prop)
  (hyp: ∀ s₁ s₂, r s₁ s₂ → bisimF r s₁ s₂) :
  ∀ s₁ s₂, r s₁ s₂ → s₁ = s₂ := @Container.M.bisim _ r (λ s₁ s₂ h₁ =>
    match h: Container.M.destruct s₁, h':Container.M.destruct s₂ with
    | (⟨.eps, k₁⟩), (⟨.eps, k₂⟩) =>
      ⟨.eps, k₁, k₂,
        by rfl, by rfl, λ i =>
        cast (by simp only [bisimF, dest, h, h']; rfl) <| hyp s₁ s₂ h₁
      ⟩
    | (⟨.cons x, k₁⟩), (⟨.cons y, k₂⟩) =>
      have hyp' := cast (by simp only [bisimF, dest, h, h']; rfl) <| hyp s₁ s₂ h₁
      ⟨.cons x, k₁, k₂,
        by rfl, by rw [hyp'.left], λ _ => by exact hyp'.2
      ⟩
    | (⟨.cons _, _⟩), (⟨.eps, _⟩) =>
      have hyp' := cast (by simp only [bisimF, dest, h, h']) <| hyp s₁ s₂ h₁
      False.elim hyp'
    | (⟨.eps, _⟩), (⟨.cons _, _⟩) =>
      have hyp' := cast (by simp only [bisimF, dest, h, h']) <| hyp s₁ s₂ h₁
      False.elim hyp'
  )


@[elab_as_elim, eliminator]
protected def Kahn.cases {motive: Kahn α → Sort w} (x: Kahn α)
  (cons: ∀ a (y: Kahn α), motive cons(a, y))
  (eps: ∀ y: Kahn α, motive eps(y))
  : motive x :=
  Container.M.cases (λ ⟨node, children⟩ =>
    match node with
    | .eps => eps (children .unit)
    | .cons x => cons x (children .unit)
  ) x

@[simp]
protected def Kahn.cases_eps {motive: Kahn α → Sort w} (x: Kahn α)
  (cons: ∀ a (x: Kahn α), motive cons(a, x))
  (eps: ∀ x: Kahn α, motive eps(x)) :
  Kahn.cases eps(x) cons eps = eps x := by
  rw [Kahn.cases]
  simp [F.mk]

@[simp]
protected def Kahn.cases_cons {motive: Kahn α → Sort w} (a: α) (x: Kahn α)
  (cons: ∀ a x, motive cons(a, x))
  (eps: ∀ x: Kahn α, motive eps(x)) :
  Kahn.cases cons(a, x) cons eps = cons a x := by
  rw [Kahn.cases]
  simp [F.mk]



open Lean Expr Elab Term Tactic Meta Qq

/-- tactic for proof by bisimulation on streams -/
syntax "kahn_bisim" (ppSpace colGt term) (" with" (ppSpace colGt binderIdent)+)? : tactic

elab_rules : tactic
  | `(tactic| kahn_bisim $e $[ with $ids:binderIdent*]?) => do
    let ids : TSyntaxArray `Lean.binderIdent := ids.getD #[]
    let idsn (n : ℕ) : Name :=
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => n.getId
        | `(binderIdent| _) => `_
        | _ => unreachable!
      | none => `_
    let idss (n : ℕ) : TacticM (TSyntax `rcasesPat) := do
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => `(rcasesPat| $n)
        | `(binderIdent| _%$b) => `(rcasesPat| _%$b)
        | _ => unreachable!
      | none => `(rcasesPat| _)
    withMainContext do
      let e ← Tactic.elabTerm e none
      let f ← liftMetaTacticAux fun g => do
        --let (#[fv], g) ← g.generalize #[{ expr := e }] | unreachable!
        let (#[fv], g) ← g.generalize #[{expr := e}] | unreachable!
        return (mkFVar fv, [g])
      withMainContext do
        let some (t, l, r) ← matchEq? (← getMainTarget) | throwError "goal is not an equality"
        let ex ←
          withLocalDecl (idsn 1) .default t fun v₀ =>
            withLocalDecl (idsn 2) .default t fun v₁ => do
              let x₀ ← mkEq v₀ l
              let x₁ ← mkEq v₁ r
              let xx ← mkAppM ``And #[x₀, x₁]
              let ex₁ ← mkLambdaFVars #[f] xx
              let ex₂ ← mkAppM ``Exists #[ex₁]
              mkLambdaFVars #[v₀, v₁] ex₂
        let R ← liftMetaTacticAux fun g => do
          let g₁ ← g.define (idsn 0) (← mkArrow t (← mkArrow t (mkSort .zero))) ex
          logWarning s!"{← inferType <| .mvar g₁}"
          let (Rv, g₂) ← g₁.intro1P
          return (mkFVar Rv, [g₂])
        withMainContext do
          ids[0]?.forM fun s => addLocalVarInfoForBinderIdent R s
          let sR ← exprToSyntax R
          evalTactic <| ← `(tactic|
            refine Kahn.bisim $sR ?_ _ _ ⟨_, rfl, rfl⟩;
            rintro $(← idss 1) $(← idss 2) ⟨$(← idss 3), $(← idss 4), $(← idss 5)⟩)
          liftMetaTactic fun g => return [← g.clear f.fvarId!]
    for n in [6 : ids.size] do
      let name := ids[n]!
      logWarningAt name m!"unused name: {name}"

#print Expr

def Kahn.dest.uniq (k k': Kahn α) :
  k.dest = k'.dest → k = k' := by
  intro h
  apply bisim (λ k k' => k.dest = k'.dest) _ _ _ h
  intro s₁ s₂ h₁
  simp only [bisimF]
  match h₂:s₁.dest, h₃:s₂.dest with
  | .eps s₁', .eps s₂' =>
    rw [h₂, h₃] at h₁
    simp only [F.eps.injEq] at h₁
    exact congrArg dest h₁
  | .cons x s₁', .cons y x₂' =>
    rw [h₂, h₃] at h₁
    simp only [F.cons.injEq] at h₁
    exact And.intro h₁.left (congrArg dest h₁.right)
  | .eps _, .cons _ _ =>
    rw [h₂, h₃] at h₁
    simp only at h₁
  | .cons _ _, .eps _ =>
    rw [h₂, h₃] at h₁
    simp only at h₁


@[simp] def Kahn.mk_dest (k:Kahn α) : k.dest.mk = k := by
  apply dest.uniq
  simp only [dest_mk]


-- remove the first `n` ε of a stream `k`
def Kahn.burn (k: Kahn α) : Nat → Kahn α
| n+1 =>
  match k.dest with
  | .eps k => burn k n
  | _ => k
| _ => k

@[simp] def Kahn.burn_cons (a: α) (k: Kahn α) (n: Nat) :
  burn (F.cons a k).mk n = (F.cons a k).mk := by
  cases n with
  | zero => simp [burn]
  | succ _ => simp [burn]

@[simp] def Kahn.burn_eps (k: Kahn α) (n: Nat) :
  burn (F.eps k).mk (n+1) = burn k n := by
  rfl

@[simp] def Kahn.burn_zero (k: Kahn α) :
  burn k 0 = k := by rfl


def Kahn.burn1_burn (k: Kahn α) (n: Nat) :
  burn (k.burn n) 1 = k.burn (n+1) := by
  induction n generalizing k with
  | zero =>
    simp only [burn, mk_dest, Nat.succ.injEq]
  | succ n h =>
    cases k using Kahn.cases with
    | cons x xs =>
      simp only [burn_cons]
    | eps xs =>
      rw [burn_eps, burn_eps]
      apply h

def Kahn.burn_burn1 (k: Kahn α) (n: Nat) :
  burn (k.burn 1) n = k.burn (n+1) := by
  cases n with
  | zero =>
    simp only [burn, mk_dest, Nat.succ.injEq]
  | succ n =>
    cases k using Kahn.cases with
    | cons x xs =>
      simp only [burn_cons]
    | eps xs =>
      rw [burn_eps, burn_eps, burn_zero]


-- rewrite a composition of burn at the burn of the sum of the fuels
theorem Kahn.burn_burn (k: Kahn α) (n m: Nat) :
  (k.burn n).burn m = k.burn (n+m) := by
  induction m generalizing n with
  | zero =>
    simp [burn]
  | succ m h =>
    specialize h (n+1)
    cases k using Kahn.cases with
    | cons a k =>
      rw [burn_cons, burn_cons, burn_cons]
    | eps k =>
      have h₁ : n + 1 + m = (n + m) + 1 := by simp_arith
      have h₂ : n + Nat.succ m = (n + m) + 1 := by simp_arith
      have h₃ : Nat.succ m = m + 1 := by simp_arith
      rw [h₁, burn_eps, burn_eps] at h
      rw [h₂, burn_eps, ←h, h₃, ←burn_burn1, burn1_burn, ←burn_burn1]
      rfl


def Kahn.ε (k: Kahn α) (n:Nat) : Kahn α :=
  match n with
  | n+1 => F.mk (.eps (k.ε n))
  | 0 => k

def Kahn.burn_ε (k: Kahn α) (n: Nat) :
  (k.ε n).burn n = k := by
  induction n with
  | zero => rfl
  | succ n h =>
    rw [ε, burn_eps]
    assumption

def Kahn.ε_ε (k: Kahn α) (n m: Nat) :
  (k.ε n).ε m = k.ε (n + m) := by
  induction m with
  | zero =>
    rfl
  | succ m h =>
    simp only [ε, ε, Nat.add_eq, h]

--theorem Kahn.burn.double_cons (a₁ a₂: α) (k k₁ k₂: Kahn α) (n m: Nat) :
--  k.burn n = F.cons a₁ k₁ → k.burn m = F.cons a₂ k₂ → k.burn n = k.burn m := by
--  intro h₁ h₂
--  induction n generalizing m k
--  case zero =>
--    simp [burn] at h₁
--    cases m with
--    | zero =>
--      rfl
--    | succ m =>
--      unfold burn
--      rw [h₁]
--  case succ n h₃ =>
--    cases h₄:k.dest with
--    | eps k' =>
--      unfold burn at h₁
--      rw [h₄] at h₁
--      simp at h₁



def Kahn.burn.depth_prop (k: Kahn α) (n: Nat) : Prop := cons? (k.burn n).dest

noncomputable def Kahn.burn_depth (k: Kahn α) : Nat :=
  Classical.epsilon (burn.depth_prop k)

-- like burn but we don't look at the depth of the search
partial def Kahn.burnAllImpl (k: Kahn α) (h₁: ¬k.bot?) : Kahn α :=
  match h₂: k.dest with
  | .eps k' =>
    k'.burnAllImpl (by
        rw [bot?]
        intro h₃
        apply h₁
        rw [h₃] at h₂;
        rw [←dest_bot] at h₂
        have h₂ := dest.uniq _ _ h₂
        rw [h₂]
        rfl
      )
  | _ => k

-- AXIOM: `burnAllImpl k` terminate and return `k.burn k.burn_depth`
@[implemented_by Kahn.burnAllImpl] def Kahn.burnAll (k: Kahn α) (h₁: ¬ k.bot?) : Kahn α :=
  k.burn k.burn_depth

#check Classical.epsilon_spec

theorem Kahn.bot_from_burn (k: Kahn α) (h: ¬ (∃ n, cons? (k.burn n).dest)) : k = bot := by
  apply bisim (λ x y => ¬(∃ n, cons? (x.burn n).dest) ∧ y = bot) _ _ _ ⟨h, Eq.refl _⟩
  intro s₁ s₂ ⟨h₁, h₂⟩
  rw [bisimF]
  match h:s₁.dest, h':s₂.dest with
  | .eps s₁', .eps s₂' =>
    simp only [not_exists]
    constructor
    . intro n h₃
      apply h₁
      exists (.succ n)
      have : burn s₁ (.succ n) = burn s₁' n := by
        rw [burn, h]
      rw [this]
      assumption
    . have h₂ := congrArg dest h₂
      simp [h', dest_bot] at h₂
      assumption
  | _, .cons _ _ =>
    have h₂ := congrArg dest h₂
    rw [h'] at h₂
    cases h₂
  | .cons _ _, .eps _ =>
    simp only [not_exists] at h₁
    specialize h₁ 0
    simp [cons?, burn, h] at h₁

-- prove that if `k` is not `⊥ ` then `k.burnAll` really burn all the epsilons
@[simp] theorem Kahn.burnAll_cons? (k: Kahn α) (h₁: ¬k.bot?) : cons? (k.burnAll h₁).dest := by
  have := @Classical.epsilon_spec _ (burn.depth_prop k)
  apply this
  have := h₁.comp (bot_from_burn k)
  have := Classical.not_not.1 this
  exact this

inductive Kahn.leF (r: Kahn α → Kahn α → Prop) : Kahn α → Kahn α → Prop where
| cons (a: α) (x y: Kahn α) (n: Nat) :
  r x y → leF r (F.cons a x).mk ((F.cons a y).mk.ε n)
| eps {x y: Kahn α} (x': Kahn α) :
  x.dest = .eps x' → r x' y → leF r x y

def Kahn.leF' : (Kahn α → Kahn α → Prop) →o (Kahn α → Kahn α → Prop) where
  toFun := leF
  monotone' := by
    intro p q h₁ k₁ k₂ h₂
    induction h₂ with
    | eps x' h₂ =>
      apply leF.eps x'
      . assumption
      . apply h₁
        assumption
    | cons a x' y' n h₂ h₃ h₄ =>
      apply leF.cons a x' y' n h₂ h₃
      . apply h₁
        assumption

@[simp] theorem Kahn.leF'.def (r: Kahn α → Kahn α → Prop) (x y: Kahn α) :
  leF' r x y = leF r x y := by rfl


instance : ScottContinuousNat (@Kahn.leF' α) where
  scottContinuousNat := by
    intro S x y h₁
    simp only [infᵢ_apply, infᵢ_Prop_eq] at h₁
    simp only [Kahn.leF'.def, infᵢ_apply, infᵢ_Prop_eq]
    have h₂ := h₁ 0
    induction h₂ with
    | eps x' h₂ h₃ =>
      apply Kahn.leF.eps x'
      . assumption
      . simp only [infᵢ_apply, infᵢ_Prop_eq]
        intro n
        specialize h₁ n
        cases h₁ with
        | cons _ _ _ _ h₄ =>
          rw [h₂] at h₄
          cases h₄
        | eps _ h₄ h₅ =>
          rw [h₂] at h₄
          simp only [Kahn.F.eps.injEq] at h₄
          rw [←h₄] at h₅
          assumption
    | cons a x' y' n h₂ h₃ h₄ =>
      apply Kahn.leF.cons a x' y' n  h₂ h₃
      simp only [infᵢ_apply, infᵢ_Prop_eq]
      intro i
      specialize h₁ i
      cases h₁ with
      | eps _ h₅ h₆ =>
        rw [h₂] at h₅
        cases h₅
      | cons _ _ _ m h₅ h₆ h₇ =>
        rw [h₂] at h₅
        simp only [Kahn.F.cons.injEq] at h₅
        rw [←h₅.right] at h₇
        sorry





