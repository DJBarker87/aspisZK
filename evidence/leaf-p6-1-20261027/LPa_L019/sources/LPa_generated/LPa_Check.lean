import XRk_FunsExternal
import LPa_Fold
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Check
-- Named native stage bridge: compact::LPa_compact::LPa_check_stage (K001).
def predicate (bs : List U8) (i : Nat) : Bool :=
  XRk_Bytes.validChunk 4 false ((bs.drop (16*i)).take 16)
def loop (bs : List U8) : Bool :=
  LPa.stages (fun good i => good && predicate bs i) true (bs.length/16)

theorem loop_eq_model (bs : List U8) :
    loop bs = XRk_Bytes.chunksValid 16 4 false bs := by
  exact LPa.stages_all (predicate bs) (bs.length/16)

theorem shipped_leaf_model (bs : Slice U8) :
    compact.check_values bs = ok (if loop bs.val then .Ok () else .Err .NonCanonical) := by
  rw [loop_eq_model]
  rfl

theorem loop_eq_fold (bs : List U8) :
    loop bs = (List.range (bs.length/16)).foldl
      (fun good i => good && predicate bs i) true :=
  LPa.stages_fold _ _ _

#print axioms loop_eq_model
#print axioms shipped_leaf_model
#print axioms loop_eq_fold
end LPa.Check
