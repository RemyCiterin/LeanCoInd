import Lean.Meta.Eqns
import Batteries.Lean.NameMapAttribute
import Lean.Elab.Exception
import Lean.Elab.InfoTree.Main

/-! # The `@[eqns]` attribute
This file provides the `eqns` attribute as a way of overriding the default equation lemmas. For
example
```lean4
def transpose {m n} (A : m → n → ℕ) : n → m → ℕ
| i, j => A j i
theorem transpose_apply {m n} (A : m → n → ℕ) (i j) :
  transpose A i j = A j i := rfl
attribute [eqns transpose_apply] transpose
theorem transpose_const {m n} (c : ℕ) :
    transpose (fun (i : m) (j : n) => c) = fun j i => c := by
  funext i j -- the rw below does not work without this line
  rw [transpose]
```
-/
open Lean Elab

syntax (name := eqns) "eqns" (ppSpace ident)* : attr

initialize eqnsAttribute : NameMapExtension (Array Name) ←
  registerNameMapAttribute {
    name  := `eqns
    descr := "Overrides the equation lemmas for a declaration to the provided list"
    add   := fun
    | declName, `(attr| eqns $[$names]*) => do
      if let some _ := Meta.eqnsExt.getState (← getEnv) |>.map.find? declName then
        throwError "There already exist stored eqns for '{declName}'; registering new equations \
          will not have the desired effect."
      names.mapM realizeGlobalConstNoOverloadWithInfo
    | _, _ => Lean.Elab.throwUnsupportedSyntax }

initialize Lean.Meta.registerGetEqnsFn (fun name => do
  pure (eqnsAttribute.find? (← getEnv) name))
