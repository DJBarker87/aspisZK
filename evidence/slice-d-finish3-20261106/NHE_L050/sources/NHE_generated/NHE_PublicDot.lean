import NHE_CheckedScalar
set_option autoImplicit false
namespace NHE_PublicDot
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := NHE_DotState.Dot
abbrev NE := FIo_Install.NE
abbrev NQ := NHE_CheckedScalar.NQ

def toWide (x : NE) : AspisR1EbyKPushDotBackend.PushWide :=
 ⟨NHE_CheckedScalar.toPush x.c0,NHE_CheckedScalar.toPush x.c1⟩
def reply (p : core.result.Result Unit Unit × Dot) := (p.1,NHE_DotState.toPush p.2)

theorem cohort (d : Dot) (value : NE) (scalar : NQ) :
 FIo_FieldBridge.map reply (FIo_Native.fast_pairing.EbyKDot.push d value scalar)=
 AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
  (NHE_DotState.toPush d) (toWide value) (NHE_CheckedScalar.toPush scalar) := by
 rw [←NFG_PublicG.source]
 unfold AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion AspisR1EbyKPushExplicitOpsV1.pushWithOps
 simp only [AspisR1EbyKPushExplicitOpsV1.maxTerms,FIo_Native.fast_pairing.MAX_TERMS,NHE_DotState.toPush,NFG_PublicG.run,←NHE_CheckedScalar.checked]
 by_cases count : d.count >= 4096#usize
 · simp only [count,if_true,FIo_FieldBridge.map,reply,NHE_DotState.toPush]
 · have cap : 8192<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
   have cv : d.count.val<4096 := by scalar_tac
   have next := FIo_ScalarBridge.add d.count 1#usize (by change d.count.val+1<UScalar.size .Usize;omega)
   have wide : AspisR1EbyKPushWideToQ.fromWide (toWide value)=ok (Array.make 2#usize [NFE_NFC_CalleeDomains.q value.c0,NFE_NFC_CalleeDomains.q value.c1]) := by
    rw [AspisR1EbyKPushWideToQ.fromWide_coordinates]
    rfl
   have i0 (a b : FIo_Native.fast_pairing.canonical.Q) : Array.index_usize (Array.make 2#usize [a,b]) 0#usize=ok a := rfl
   have i1 (a b : FIo_Native.fast_pairing.canonical.Q) : Array.index_usize (Array.make 2#usize [a,b]) 1#usize=ok b := rfl
   simp only [count,if_false,wide,i0,i1,NHE_CheckedScalar.checked,NFG_PublicG.check_result,bind_tc_ok]
   split_ifs
   all_goals simp_all only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame,lift,FIo_FieldBridge.map_bind,←NHE_PrivateDot.cohort,bind_assoc_eq,next,NHE_PrivateDot.toPush,NFE_NFC_CalleeDomains.q]
   all_goals try rfl

#print axioms cohort
end NHE_PublicDot
