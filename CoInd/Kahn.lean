
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

def Kahn.F.mk.inj (k k': F α (Kahn α)) :
  k.mk = k'.mk → k = k' := by
  intro h
  have h := congrArg dest h
  rw [dest_mk, dest_mk] at h
  assumption

@[simp] def Kahn.F.mk.injEq (k k': F α (Kahn α)) :
  (k.mk = k'.mk) = (k = k') := by
  apply propext
  constructor
  . apply inj
  . apply congrArg


macro "eps(" t:term ")" : term => `(Kahn.F.mk (Kahn.F.eps $t))
macro "cons(" a:term "," t:term ")" : term => `(Kahn.F.mk (Kahn.F.cons $a $t))


open Lean PrettyPrinter Delaborator Meta Expr SubExpr Qq in
@[delab app.Kahn.F.mk]
def Kahn.F.mk.delab : Delab := do
  let e ← instantiateMVars <| ← getExpr
  let t ← whnf (← inferType e)
  let .sort (.succ u) ← whnf (← inferType t) | failure
  have t : Q(Type u) := t
  have e : Q($t) := e
  go u t e
where
  fallBack : DelabM Term := do
    guard False
    failure

  go (u: Level) (t: Q(Type u)) (expr: Q($t)) : DelabM Term :=
    match t with
    | ~q(Container.M (Kahn.C $typ)) =>
      match expr with
      | ~q(Kahn.F.mk (Kahn.F.eps $e)) => do
        let e := (← delabCore e default Delaborator.delab).fst
        `(eps($e))
      | ~q(Kahn.F.mk (Kahn.F.cons $a $e)) => do
        let a := (← delabCore a default Delaborator.delab).fst
        let e := (← delabCore e default Delaborator.delab).fst
        `(cons($a, $e))
      | _ =>
        fallBack
    | _ =>
      fallBack

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

def Kahn.dest.inj (k k': Kahn α) :
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

@[simp] def Kahn.dest.injEq (k k': Kahn α) :
  (k.dest = k'.dest) = (k = k') := by
  apply propext
  constructor
  . apply inj
  . apply congrArg


@[simp] def Kahn.mk_dest (k:Kahn α) : k.dest.mk = k := by
  apply dest.inj
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


-- rewrite a composition of burn at the burn of the sum of the fuels
theorem Kahn.burn_compose (k: Kahn α) (n m: Nat) :
  (k.burn n).burn m = k.burn (n+m) := by
  induction n generalizing m k with
  | zero =>
    simp [burn]
  | succ n h =>
    cases k using Kahn.cases with
    | eps xs =>
      have h' : Nat.succ n + m = Nat.succ (n+m) := by simp_arith
      simp only [h', burn]
      apply h
    | cons x xs =>
      simp only [burn, dest_mk, burn_cons]

theorem Kahn.burn_cons_inj (x y: α) (xs ys k: Kahn α) (n m: Nat) :
  k.burn n = cons(x, xs) → k.burn m = cons(y, ys) → x = y ∧ xs = ys := by
  intro h₁ h₂
  have h₃ := congrArg (λ k => burn k m) h₁
  have h₄ := congrArg (λ k => burn k n) h₂
  simp only [burn_compose, burn_cons] at h₃ h₄
  rw [Nat.add_comm, h₃, Kahn.F.mk.injEq, F.cons.injEq] at h₄
  assumption

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
        have h₂ := dest.inj _ _ h₂
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
| cons {x y: Kahn α} (a: α) (xs ys: Kahn α) (n: Nat) :
  x.dest = .cons a xs → (y.burn n).dest = .cons a ys → r xs ys → leF r x y
| eps {x y: Kahn α} (xs: Kahn α) :
  x.dest = .eps xs → r xs y → leF r x y

-- A monotone version of the less than functor
def Kahn.leF.mono : (Kahn α → Kahn α → Prop) →o (Kahn α → Kahn α → Prop) where
  toFun := leF
  monotone' := by
    intro p q h₁ k₁ k₂ h₂
    induction h₂ with
    | eps xs h₂ h₃ =>
      apply leF.eps xs h₂
      apply h₁
      assumption
    | cons a xs ys n h₂ h₃ h₄ =>
      apply leF.cons a xs ys n h₂ h₃
      apply h₁
      assumption


@[simp] theorem Kahn.leF.mono.def (r: Kahn α → Kahn α → Prop) (x y: Kahn α) :
  leF.mono r x y = leF r x y := by rfl

-- proof of the Scott Continuity of `leF`
instance Kahn.leF.SC : ScottContinuousNat (@Kahn.leF.mono α) where
  scottContinuousNat := by
    intro S x y h₁
    simp only [infᵢ_apply, infᵢ_Prop_eq] at h₁
    simp only [Kahn.leF.mono.def, infᵢ_apply, infᵢ_Prop_eq]
    have h₂ := h₁ 0
    induction h₂ with
    | eps xs h₂ h₃ =>
      apply Kahn.leF.eps xs h₂
      simp only [infᵢ_apply, infᵢ_Prop_eq]
      intro i
      specialize h₁ i
      cases h₁ with
      | eps xs h₁ h₄ =>
        rw [h₁, F.eps.injEq] at h₂
        induction h₂
        assumption
      | cons a xs ys n h₁ h₄ h₅ =>
        rw [h₁] at h₂
        cases h₂
    | cons a xs ys n h₂ h₃ _ =>
      apply leF.cons a xs ys n  h₂ h₃
      simp only [infᵢ_apply, infᵢ_Prop_eq]
      intro i
      specialize h₁ i
      cases h₁ with
      | eps _ h₅ h₆ =>
        rw [h₂] at h₅
        cases h₅
      | cons _ _ _ m h₅ h₆ h₇ =>
        rw [h₂, F.cons.injEq] at h₅
        induction h₅.1
        induction h₅.2
        have h₃ := congrArg F.mk h₃
        have h₆ := congrArg F.mk h₆
        rw [mk_dest] at h₃ h₆
        have := burn_cons_inj _ _ _ _ _ _ _ h₃ h₆
        rw [this.2]
        assumption

instance Kahn.LE.inst : LE (Kahn α) where
  le := OrderHom.gfp Kahn.leF.mono

def Kahn.le.approx (n: Nat) (lhs rhs: Kahn α) : Prop :=
  match n with
  | 0   => True
  | n+1 => leF (le.approx n) lhs rhs

#check gfp.scott.unfold

def Kahn.le.unfold (x y: Kahn α) : ((x ≤ y) = leF LE.le x y) := by
  simp only [LE.le, gfp.scott.rewrite]
  conv =>
    lhs
    rw [←gfp.scott.unfold]
    rfl

#check pgfp.accumulate
#check pgfp.unfold
#print pgfp.scott
#check pgfp.theorem₂ (@Kahn.leF.mono α)

def Kahn.le.rewrite (k₁ k₂: Kahn α) :
  k₁ ≤ k₂ ↔ (∀ n, Kahn.le.approx n k₁ k₂) := by
  simp only [LE.le, gfp.scott.rewrite, gfp.scott, infᵢ_apply, infᵢ_Prop_eq]
  constructor
  . intro h n
    specialize h n
    induction n generalizing k₁ k₂ with
    | zero => trivial
    | succ n h' =>
      cases h with
      | eps xs h₁ h₂ =>
        rw [approx]
        apply leF.eps xs h₁
        apply h'
        assumption
      | cons a xs ys m h₁ h₂ h₃ =>
        rw [approx]
        apply leF.cons a xs ys m h₁ h₂
        apply h'
        apply h₃
  . intro h n
    specialize h n
    induction n generalizing k₁ k₂ with
    | zero => trivial
    | succ n h' =>
      rw [approx] at h
      cases h with
      | eps xs h₁ h₂ =>
        apply leF.eps xs h₁
        apply h'
        apply h₂
      | cons a xs ys m h₁ h₂ h₃ =>
        apply leF.cons a xs ys m h₁ h₂
        apply h'
        apply h₃

def Kahn.le.refl (x: Kahn α) : x ≤ x := by
  have h: ∀ n, burn x n ≤ x := by
    intro n
    rw [Kahn.le.rewrite]
    intro m
    induction m generalizing n x with
    | zero => trivial
    | succ m h₁ =>
      rw [approx]
      generalize h₂: burn x n = y
      cases y using Kahn.cases with
      | eps ys =>
        apply leF.eps ys
        . rw [←F.mk.injEq, mk_dest]
        . have h₂ := congrArg (fun k => k.burn 1) h₂
          simp only [burn_compose, burn_eps, burn_zero] at h₂
          rw [←h₂]
          apply h₁
      | cons y ys =>
        apply leF.cons y ys ys n
        . rw [←F.mk.injEq, dest_mk]
        . rw [h₂, ←F.mk.injEq, dest_mk]
        . conv =>
            arg 2
            . rw [←burn_zero ys]
              rfl
          apply h₁
  apply h 0

def Kahn.le_imp_eps_le (x y: Kahn α) (h₁: x ≤ y) : eps(x) ≤ y := by
  rw [Kahn.le.unfold]
  apply leF.eps x
  . rfl
  . assumption

def Kahn.eps_le_imp_le (x y: Kahn α) (h₁: eps(x) ≤ y) : x ≤ y := by
  rw [Kahn.le.unfold] at h₁
  cases h₁
  <;> sorry


