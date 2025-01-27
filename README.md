# LeanCoInd


This repo describe an implementation of Kahn networks (finite or infinite
streams in Lean4), It contain multiple parts:
1. Definition of coinductive types using polynomial functors in Conainter.lean,
   M.lean, MIdx.lean...
2. Properties and tactics about coinductive types in Paco.lean and Tactics.lean
3. Properties about omega complete partial orders, theses definition are used to
   define fixed point over Khan networks and notion of continuous
   functions/safety properties (named Admissible here)
4. Definition of Kahn networks in Kahn.lean, a Kahn network is essencially a
   finite or infinite stream defined using a polynomial functor
   $$Kahn X := bot | cons X (Kahn X)$$
5. Tactics about Kahn networks like

```lean
open Kahn OmegaPartialOrder.ContinuousHom.Kahn

defnode foo (X: Kahn Int, Y: Kahn Int) := Z
    where
        Z : Kahn Int := fby(Init, X)
        Init : Kahn Int := (X == Y ? 1 : 0)

defprop foo.pre => (X: Kahn Int, Y: Kahn Int) :=
    0 < X

defprop foo.inv1 => (X: Kahn Int, Y: Kahn Int) (Z: Kahn Int, Init: Kahn Int) :=
    0 < Z

defprop foo.inv2 => (X: Kahn Int, Y: Kahn Int) (Z: Kahn Int, Init: Kahn Int) :=
    0 < Init
```

The implementation of coinductives types (M-types and indexed M-types) is based on
["Data types as quotients of polynomial functor"](http://www.contrib.andrew.cmu.edu/~avigad/Papers/qpf.pdf).
With a generalization to indexed polynomial functors


I also try to define a LTL logic over finite or infinite streams compatible with
the notion of admissible properties (such that P \entails Q is admissible in Q),
but their is an issue because entails is not transitive in this case :
    if $Q = \bottom$, then $P \entails Q$ and $Q \entails R$ but their is no
    reason for $P \entails R$

Classifying discrete temporal properties
