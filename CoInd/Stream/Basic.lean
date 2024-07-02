import CoInd.M
import CoInd.MIdx
import CoInd.Paco
import CoInd.Container
import CoInd.Utils

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

def node.indution (env: node.tenv) (eqs: equation env) (inv: invariant env) :
  (∀ e: eval env, eqs e → inv e.get_state → inv e.tail.get_state) →
  ∀ e:eval env, eqs e → inv e.get_state → (forall_inv inv e)
  := by sorry

def node.tenv.test : tenv := [Nat, Nat, Bool]

def node.eval.test : node.eval node.tenv.test :=
  Cons (stream.const 1) (Cons (stream.const 2) (Cons (stream.const false) Nil))
