import LPl_Kit_FunsExternal
import LPl_A_Fold
open Aeneas Aeneas.Std Result
open LPl_Kit_Release
set_option autoImplicit false
namespace LPl_A.Echeck
-- Native stage bridge: verifier::LPl_A_verifier::LPl_A_echeck_stage (K008).
def predicate (bs : List U8) (k : Bool) (i : Nat) : Bool :=
  LPl_Kit_Bytes.validChunk 8 k ((bs.drop (32*i)).take 32)
def loop (bs : List U8) (k : Bool) : Bool :=
  LPl_A.stages (fun good i => good && predicate bs k i) true (bs.length/32)
theorem loop_eq_model (bs : List U8) (k : Bool) :
    loop bs k = LPl_Kit_Bytes.chunksValid 32 8 k bs :=
  LPl_A.stages_all _ _
theorem shipped_leaf_model (bs : Slice U8) (k : Bool) :
    verifier.echeck bs k = ok (if loop bs.val k then .Ok () else .Err .Parse) := by
  rw [loop_eq_model]
  rfl
theorem loop_eq_fold (bs : List U8) (k : Bool) :
    loop bs k = (List.range (bs.length/32)).foldl
      (fun good i => good && predicate bs k i) true :=
  LPl_A.stages_fold _ _ _
#print axioms loop_eq_model
#print axioms shipped_leaf_model
#print axioms loop_eq_fold
end LPl_A.Echeck
