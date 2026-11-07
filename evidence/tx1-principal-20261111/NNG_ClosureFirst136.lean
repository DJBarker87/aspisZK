import NNG_Array136
set_option autoImplicit false
namespace AspisR1.NNG_ClosureFirst136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Array136

/-- Actual emitted closure, one arbitrary entered first-array index. It
returns exactly claims[0][i] and preserves the captured Claims value. -/
theorem source {H : Type} (d : aspis_core.digest.Digest32 H) (claims : Claims)
    (i : Usize) (hi : i.val < 16) :
    r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut d claims i =
      .ok (cell claims i (by omega), claims) := by
  have h29 : i.val < 29 := by omega
  unfold r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [NNG_Array136.index claims 0#usize (by decide), bind_tc_ok]
  change (do let q ← Array.index_usize (row0 claims) i; ok (q,claims)) = _
  rw [NNG_Array136.index (row0 claims) i h29, bind_tc_ok]
  rfl
#print axioms source
end AspisR1.NNG_ClosureFirst136
