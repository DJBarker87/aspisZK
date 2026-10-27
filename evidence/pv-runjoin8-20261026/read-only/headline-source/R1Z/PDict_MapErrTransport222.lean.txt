import R1Z.PDict_CopyLoop222
import R1Z.PDict_CurrentCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_MapErrTransport222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

/-- Precise pure callback field law, discharged for the current selector below. -/
def MapErrLaw (b : ExternalTypes) (ops : @ExternalFuns b) : Prop :=
  @ExternalFuns.op12 b ops = @ProverRwOuterMapErr.map_err

theorem current_map_err (b : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native b)) :
    MapErrLaw (PDict_CodecDictionary.native b) (PDict_CodecDictionary.selected b ops) := by
  rfl

theorem map_err_inner {A B E E' O : Type} (f : A → B)
    (inst : core.ops.function.FnOnce O E E') (r : core.result.Result A E) (c : O) :
    ProverRwOuterMapErr.map_err inst (innerMap f r) c =
      resultMap (innerMap f) (ProverRwOuterMapErr.map_err inst r c) := by
  cases r with
  | Ok a => rfl
  | Err e =>
    simp only [ProverRwOuterMapErr.map_err, innerMap, PDict_ResultTransport.map_bind]
    cases inst.call_once c e <;> rfl

#print axioms current_map_err
#print axioms map_err_inner
end R1Z.PDict_MapErrTransport222
