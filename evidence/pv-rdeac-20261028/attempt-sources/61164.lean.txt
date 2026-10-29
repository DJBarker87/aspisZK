import R1Z.PV_CBL_DigestDefaultValue
import R1Z.PV_CBL_DigestUpdateTotal
import R1Z.PV_CBL_FinalizeSoftTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestSoftTotal
set_option autoImplicit false
/-- The complete fixed owned SHA-256 reference is total on every sized Slice.
This does not identify the native generic wrapper or selected CPU backend. -/
theorem total (data : Slice U8) : ∃ output, PV_CBL_DigestSoft.sha_digest_soft_owned data=ok output := by
  obtain ⟨updated,hu,hp⟩ := PV_CBL_DigestUpdateTotal.total
    PV_CBL_DigestDefaultValue.state 0#u64 (Array.repeat 64#usize 0#u8) 0#usize data (by decide)
  obtain ⟨final,hf⟩ := PV_CBL_FinalizeSoftTotal.total updated.1 updated.2.1 updated.2.2.1 updated.2.2.2 hp
  refine ⟨final.1,?_⟩
  unfold PV_CBL_DigestSoft.sha_digest_soft_owned
  rw [PV_CBL_DigestDefaultValue.source,bind_tc_ok]
  change (do
    let q ← PV_CBL_DigestSoft.sha_update_soft_owned PV_CBL_DigestDefaultValue.state 0#u64
      (Array.repeat 64#usize 0#u8) 0#usize data
    let f ← PV_CBL_FinalSoft.sha_finalize_soft_owned q.1 q.2.1 q.2.2.1 q.2.2.2
    ok f.1) = _
  rw [hu,bind_tc_ok,hf,bind_tc_ok]
#print axioms total
end R1Z.PV_CBL_DigestSoftTotal
