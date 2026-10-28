import R1Z.PV_CBL_DigestSoftTotal
import R1Z.PV_CBL_DigestUpdateSource
import R1Z.PV_CBL_FinalizeSoftSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestSoftSource
set_option autoImplicit false
def updated (data : Slice U8) : PV_CBL_DigestUpdateStep.Snapshot :=
  PV_CBL_DigestUpdateModel.value
    (PV_CBL_DigestDefaultValue.state,0#u64,Array.repeat 64#usize 0#u8,0#usize) data.val
theorem eager (data : Slice U8) : (updated data).2.2.2.val<64 := by
  obtain ⟨out,hr,hp⟩ := PV_CBL_DigestUpdateTotal.total PV_CBL_DigestDefaultValue.state
    0#u64 (Array.repeat 64#usize 0#u8) 0#usize data (by decide)
  rw [PV_CBL_DigestUpdateSource.source _ _ _ _ _ (by decide)] at hr
  cases hr
  exact hp
def value (data : Slice U8) : Array U8 32#usize :=
  let q := updated data
  PV_CBL_DigestBytesValue.value (PV_CBL_FinalizeSoftSource.state q.1 q.2.1 q.2.2.1 q.2.2.2 (eager data))
theorem source (data : Slice U8) : PV_CBL_DigestSoft.sha_digest_soft_owned data=ok (value data) := by
  unfold PV_CBL_DigestSoft.sha_digest_soft_owned
  rw [PV_CBL_DigestDefaultValue.source,bind_tc_ok]
  change (do
    let q ← PV_CBL_DigestSoft.sha_update_soft_owned PV_CBL_DigestDefaultValue.state 0#u64
      (Array.repeat 64#usize 0#u8) 0#usize data
    let f ← PV_CBL_FinalSoft.sha_finalize_soft_owned q.1 q.2.1 q.2.2.1 q.2.2.2
    ok f.1) = _
  rw [PV_CBL_DigestUpdateSource.source _ _ _ _ _ (by decide),bind_tc_ok]
  change (do
    let f ← PV_CBL_FinalSoft.sha_finalize_soft_owned (updated data).1 (updated data).2.1
      (updated data).2.2.1 (updated data).2.2.2
    ok f.1) = _
  rw [PV_CBL_FinalizeSoftSource.source (updated data).1 (updated data).2.1
    (updated data).2.2.1 (updated data).2.2.2 (eager data),bind_tc_ok]
  rfl
#print axioms updated
#print axioms eager
#print axioms value
#print axioms source
end R1Z.PV_CBL_DigestSoftSource
