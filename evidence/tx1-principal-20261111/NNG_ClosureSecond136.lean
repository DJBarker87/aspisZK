import NNG_Array136
import NNG_Offset16
set_option autoImplicit false
namespace AspisR1.NNG_ClosureSecond136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Array136 NNG_Offset16

/-- The actual second-array closure uses 16+i on the ten entered indices.
It returns the exact Claims cell and the identical captured Claims value. -/
theorem source {H : Type} (d : aspis_core.digest.Digest32 H) (claims : Claims)
    (i : Usize) (hi : i.val < 10) :
    r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut d claims i =
      .ok (cell claims (shifted i) (bound i hi), claims) := by
  unfold r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  change (do
    let a ← Array.index_usize claims 0#usize
    let q ← Array.index_usize a (shifted i)
    ok (q,claims)) = _
  rw [NNG_Array136.index claims 0#usize (by decide), bind_tc_ok]
  change (do let q ← Array.index_usize (row0 claims) (shifted i); ok (q,claims)) = _
  rw [NNG_Array136.index (row0 claims) (shifted i) (bound i hi), bind_tc_ok]
  rfl
#print axioms source
end AspisR1.NNG_ClosureSecond136
