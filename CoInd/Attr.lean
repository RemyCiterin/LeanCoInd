import Mathlib.Tactic.LabelAttr



namespace Mathlib.Tactic.OmegaCompletePartialOrder.Admissible

namespace Attr

syntax (name := refinment_type) "refinment_type" : attr

open LabelAttr in

initialize ext : LabelExtension ← (
  let descr := "A lemma proving the typing of an element of an ω-CPO by an admissible property"
  let refinment_type := `refinment_type
  registerLabelAttr refinment_type descr refinment_type)
