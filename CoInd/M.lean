import Qq
import Lean
import CoInd.Container
import Lean
import Std
import CoInd.Paco

namespace Container
variable {C:Container.{u₁}}


inductive Approx (C:Container) : Nat → Type _ where
| MStep : {n:Nat} → (node:C.A) → (children:C.B node → Approx C n) → Approx C (.succ n)
| MStop : Approx C 0

#check @Approx

def Approx.node {n:Nat} : Approx C (.succ n) →  C.A
| .MStep node _ => node

def Approx.children {n:Nat} : (approx:Approx C (.succ n)) → C.B approx.node → Approx C n
| .MStep _ children => children

inductive Agree : ∀ {n:Nat}, Approx C n → Approx C (.succ n) → Prop where
| AgreeStep : {n:Nat} → (node:C.A) →
  (k₁:C.B node → Approx C n) →
  (k₂:C.B node → Approx C (.succ n)) →
  (∀ x, Agree (k₁ x) (k₂ x)) →
  Agree (Approx.MStep node k₁) (Approx.MStep node k₂)
| AgreeStop : ∀ x, Agree (.MStop) x

def Agree.toExists {n:Nat} (a₁:Approx C (.succ n)) (a₂:Approx C (.succ (.succ n)))
  (agree:Agree a₁ a₂) : ∃ node k₁ k₂,
    a₁ = Approx.MStep node k₁ ∧ a₂ = Approx.MStep node k₂ ∧ (∀ arg:C.B node, Agree (k₁ arg) (k₂ arg)) :=
by
  cases agree with
  | AgreeStep node k₁ k₂ h =>
    exact ⟨node, k₁, k₂, by rfl, by rfl, h⟩

structure M (C:Container.{u₁}) where
  approx: ∀ n, Approx C n
  agrees: ∀ n, Agree (approx n) (approx (.succ n))

def M.node (m: M C) : C.A :=
  (m.approx 1).node

def M.node_thm (m:M C) (n:Nat) :
  (m.approx (.succ n)).node = m.node :=
by
  induction n with
  | zero =>
    rfl
  | succ n h =>
    have h₁ := m.agrees (.succ n)
    have ⟨node, k₁, k₂, h₁, h₂, h₃⟩ := Agree.toExists _ _ h₁
    rw [h₁] at h
    rw [h₂]
    simp only [Approx.node] at *
    assumption

#check Eq.mp
#check cast_heq

def Agree.children {n:Nat} (x:Approx C (.succ n)) (y:Approx C (.succ <| .succ n))
  {i j} {hₑ: HEq i j} (h₁: Agree x y) : Agree (x.children i) (y.children j) := by
  cases h₁ with
  | AgreeStep _ _ _ h =>
    cases hₑ
    apply h

def M.children (m: M C) (arg:C.B m.node) : M C where
  approx n :=
    (m.approx (.succ n)).children (cast (by rw [node_thm]) arg)

  agrees n := by
    have h₁ := m.agrees (.succ n)
    apply Agree.children _ _ h₁
    apply @HEq.trans _ (C.B m.node)
    apply cast_heq
    apply HEq.symm
    apply cast_heq

def M.destruct (m:M C) : C.Obj (M C) where
  fst := m.node
  snd := m.children

def Approx.corec {α:Type u₃} (f:α → C.Obj α) (x₀:α) : ∀ n:Nat, Approx C n
| 0 => .MStop
| .succ n =>
  .MStep (f x₀).fst (λ x => Approx.corec f ((f x₀).snd x) n)

def Agree.corec {α:Type u₃} (f:α → C.Obj α) (x₀:α) (n:Nat) :
  Agree (Approx.corec f x₀ n) (Approx.corec f x₀ (.succ n)) :=
by
  induction n generalizing x₀ with
  | zero =>
    apply AgreeStop
  | succ n h₀ =>
    apply AgreeStep
    intro x
    apply h₀

def M.corec {α:Type u₃} (f:α → C.Obj α) (x₀:α) : M C where
  approx := Approx.corec f x₀
  agrees := Agree.corec f x₀

#check Container

theorem M.destruct_corec {α:Type u₃} (f:α → C.Obj α) (x₀:α) :
  (M.corec f x₀).destruct = C.Map (M.corec f) (f x₀) := Eq.refl _

#check cast_heq

theorem Eq_from_Heq {α β:Sort u₁} (i:α) (j:β) (h₀:α=β) (h:HEq i j) : cast h₀ i = j :=
by
  cases h
  apply eq_of_heq
  apply cast_heq

theorem M.bisim.lemma0 :
  ∀ (x:M C) (n:Nat) i j, HEq i j →  (x.approx (.succ n)).children i = (x.destruct.snd j).approx n :=
by
  intro x n i j heq
  have : i = cast (by rw [node_thm]; simp [destruct]) j := by
    have : C.B x.destruct.fst = C.B (x.approx (.succ n)).node := by rw [node_thm]; simp [destruct]
    rw [Eq_from_Heq j i]
    apply HEq.symm
    assumption

  simp only [this, children, Approx.node, destruct]

#check congrArg
#check Sigma.mk

theorem M.bisim.lemma1 (R:M C → M C → Prop)
  (h₀: ∀ x y, R x y → ∃ node k₁ k₂, destruct x = ⟨node, k₁⟩ ∧ destruct y = ⟨node, k₂⟩ ∧ ∀ i, R (k₁ i) (k₂ i)) :
  ∀ x y n, R x y → x.approx n = y.approx n :=
  -- use that (x.approx n).children i = (x.destruct.snd i).approx n
by
  intro x y n h₁
  induction n generalizing x y
  case zero =>
    cases x.approx 0
    cases y.approx 0
    rfl
  case succ n h =>
    have h₂ := x.node_thm n
    have h₃ := y.node_thm n
    cases h₄: x.approx (.succ n) with
    | MStep nodex cx =>
      cases h₅: y.approx (.succ n) with
      | MStep nodey cy =>
        have ⟨node, k₁, k₂, eq₁, eq₂, kR⟩ := h₀ _ _ h₁
        have h₂ : (Approx.MStep nodex cx).node = node := by
          have := congrArg (λ x => x.1) eq₁
          simp only [destruct] at this
          rw [h₄] at h₂
          rw [←this]
          exact h₂

        --rw [h₄] at h₂

        have h₃ : (Approx.MStep nodey cy).node = node := by
          have := congrArg (λ x => x.1) eq₂
          simp only [destruct] at this
          rw [h₅] at h₃
          rw [←this]
          exact h₃

        --rw [h₅] at h₃

        simp [Approx.node] at h₂ h₃
        have h₂ := Eq.symm h₂
        have h₃ := Eq.symm h₃
        have h₆ := bisim.lemma0 x n
        have h₇ := bisim.lemma0 y n
        rw [h₄] at h₆
        rw [h₅] at h₇
        simp only [Approx.children] at h₇ h₆
        induction h₂
        induction h₃
        suffices h₈ : ∀ i: C.B node, cx i = cy i by
          have : cx = cy := by
            funext i
            apply h₈
          rw [this]
        intro i
        have h₆ : ∀ i, cx i = (k₁ i).approx n := by
          have h : ∀ i j, HEq i j → (x.destruct.snd i) = k₁ j := by
            rw [eq₁]
            intro i j heq
            cases heq
            rfl

          intro i
          rw [h₆ i (cast (by simp [congrArg (λ x => x.1) eq₁]) i)]
          . rw [h]
            apply cast_heq
          . apply HEq.symm
            apply cast_heq

        have h₇ : ∀ i, cy i = (k₂ i).approx n := by
          have h : ∀ i j, HEq i j → (y.destruct.snd i) = k₂ j := by
            rw [eq₂]
            intro i j heq
            cases heq
            rfl

          intro i
          rw [h₇ i (cast (by simp [congrArg (λ x => x.1) eq₂]) i)]
          . rw [h]
            apply cast_heq
          . apply HEq.symm
            apply cast_heq

        rw [h₆, h₇]
        apply h
        apply kR

theorem M.bisim (R:M C → M C → Prop)
  (h₀: ∀ x y, R x y → ∃ node k₁ k₂, destruct x = ⟨node, k₁⟩ ∧ destruct y = ⟨node, k₂⟩ ∧ ∀ i, R (k₁ i) (k₂ i)) :
  ∀ x y, R x y → x = y :=
by
  intro x y h₁
  suffices h₂: x.approx = y.approx by
    cases x
    cases y
    simp only  at h₂
    simp [h₂]
  funext n
  apply bisim.lemma1 R h₀ x y n h₁

#check M
#check M.corec
#check M.destruct
#check M.destruct_corec
#check M.bisim

open Lean Expr Elab Term Tactic Meta Qq

/-- tactic for proof by bisimulation -/
syntax "mv_bisim" (ppSpace colGt term) (" with" (ppSpace colGt binderIdent)+)? : tactic


elab_rules : tactic
  | `(tactic| mv_bisim $e $[ with $ids:binderIdent*]?) => do
    let ids : TSyntaxArray `Lean.binderIdent := ids.getD #[]
    let idsn (n : Nat) : Name :=
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => n.getId
        | `(binderIdent| _) => `_
        | _ => unreachable!
      | none => `_
    let idss (n : Nat) : TacticM (TSyntax `rcasesPat) := do
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
        let (#[fv], g) ← g.generalize #[{ expr := e }] | unreachable!
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
          let (Rv, g₂) ← g₁.intro1P
          return (mkFVar Rv, [g₂])
        withMainContext do
          ids[0]?.forM fun s => addLocalVarInfoForBinderIdent R s
          let sR ← exprToSyntax R
          evalTactic <| ← `(tactic|
            --refine MvQPF.Cofix.bisim₂ $sR ?_ _ _ ⟨_, rfl, rfl⟩;
            --refine Container.M.bisim $sR ?_ _ _ ⟨_, rfl, rfl⟩;
            refine Container.M.bisim $sR ?_ _ _ ⟨_, rfl, rfl⟩;
            rintro $(← idss 1) $(← idss 2) ⟨$(← idss 3), $(← idss 4), $(← idss 5)⟩)
          liftMetaTactic fun g => return [← g.clear f.fvarId!]
    for n in [6 : ids.size] do
      let name := ids[n]!
      logWarningAt name m!"unused name: {name}"
#check Container.M.bisim

end Container
