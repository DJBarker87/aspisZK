import XRk_FunsExternal
import LPa_Fold
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Echeck
-- Native stage bridge: verifier::LPa_verifier::LPa_echeck_stage (K008).
def predicate (bs : List U8) (k : Bool) (i : Nat) : Bool :=
  XRk_Bytes.validChunk 8 k ((bs.drop (32*i)).take 32)
def loop (bs : List U8) (k : Bool) : Bool :=
  LPa.stages (fun good i => good && predicate bs k i) true (bs.length/32)
theorem loop_eq_model (bs : List U8) (k : Bool) :
    loop bs k = XRk_Bytes.chunksValid 32 8 k bs :=
  LPa.stages_all _ _
theorem shipped_leaf_model (bs : Slice U8) (k : Bool) :
    verifier.echeck bs k = ok (if loop bs.val k then .Ok () else .Err .Parse) := by
  rw [loop_eq_model]
  rfl
theorem loop_eq_fold (bs : List U8) (k : Bool) :
    loop bs k = (List.range (bs.length/32)).foldl
      (fun good i => good && predicate bs k i) true :=
  LPa.stages_fold _ _ _
#print axioms loop_eq_model
#print axioms shipped_leaf_model
#print axioms loop_eq_fold
end LPa.Echeck
