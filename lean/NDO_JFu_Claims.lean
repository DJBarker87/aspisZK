import NDO_JFu_ClaimsDecode0
import NDO_JFu_ClaimsDecode1
import NDO_JFu_ClaimsDecode2
import NDO_JFu_ClaimsDecode3
import NDO_JFr_RecordsAt
import NDO_JFr_PrefixRecords
set_option autoImplicit false
namespace AspisR1.JFu_Claims
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation

theorem source (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok JFu_ClaimsData.claims) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have call := JFr_RecordsAt.source pre records 25#u8 (by change 25<27;omega) JFw_NativeRow25.record rfl
  let record : AspisR1ClaimsUnrolledParent.Record := ⟨25#u8,JFw_NativeRow25.record⟩
  have recordEq : ClaimsUnrolledFinish.toMainRecord record=JFu_Q25Source.record := rfl
  have prefixEq : ClaimsUnrolledFinish.toMainPrefix (ClaimsUnrolledFinish.fromMainPrefix pre)=pre := by cases pre;rfl
  have getter : ClaimsUnrolledFinish.sourceRecord (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8=ok (.Ok record) := by
    unfold ClaimsUnrolledFinish.sourceRecord
    rw [prefixEq,call]
  have d0 : ClaimsUnrolledFinish.sourceDecode 29#usize record 0#usize=ok (.Ok (ClaimsUnrolledFinish.fromMainArray JFu_ClaimsData.a0)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [recordEq,JFu_ClaimsData.decode0]
  have d1 : ClaimsUnrolledFinish.sourceDecode 29#usize record 29#usize=ok (.Ok (ClaimsUnrolledFinish.fromMainArray JFu_ClaimsData.a1)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [recordEq,JFu_ClaimsData.decode1]
  have d2 : ClaimsUnrolledFinish.sourceDecode 29#usize record 58#usize=ok (.Ok (ClaimsUnrolledFinish.fromMainArray JFu_ClaimsData.a2)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [recordEq,JFu_ClaimsData.decode2]
  rw [ClaimsUnrolledFinish.claims_value]
  unfold ClaimsUnrolledFinish.reference
  rw [NP6_ClaimsModel.reference_normalized]
  simp only [NP6_ClaimsModel.normalized,ClaimsUnrolledFinish.external,getter,bind_tc_ok,
    AspisR1ClaimsUnrolledParent.decodeRows,d0,d1,d2,core.result.Result.Insts.CoreOpsTry.branch]
  rfl

#print axioms source
end AspisR1.JFu_Claims
