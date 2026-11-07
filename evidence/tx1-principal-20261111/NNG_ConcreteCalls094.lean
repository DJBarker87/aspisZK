import NNG_StateCalls094
import NNG_FlushCall094
import NNG_GeometryCall094
import NNG_BatchCall094
import NNG_ScanCall094
import NNG_PrepareAdapter094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteCalls094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094
/-- The dictionary uses the SAME supplied Env and the CLOSED deterministic
child models. The checkpoint slot remains deliberately uninstalled pending
its arbitrary-public-bytes domain correction. This is support, not a root. -/
def calls (env : RSL.Env)
 (checkpoint : ∀ {H : Type}, aspis_core.digest.Digest32 H → verifier.Prepared → verifier.Accumulator →
  Slice U8 → Slice U8 → H → Result (alloc.vec.Vec U8)) : NNG_Context094.Calls where
 c0:=ok (fromT3 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO)
 c1:=NNG_ParseCall094.call env
 c2:=NNG_ScanCall094.call env
 c3:=fun _ proof p root batch _=>NNG_BatchCall094.call env proof p root batch
 c4:=fun proof p a g _ geo pending finish=>NNG_StateCalls094.queryLoop env proof p a g geo pending finish
 c5:=NNG_PrepareAdapter094.call env
 c6:=checkpoint
 c7:=NNG_FlushCall094.call
 c8:=NNG_StateCalls094.weightsNew env
 c9:=NNG_StateCalls094.geometry env
 c10:=fun _=>NNG_StateCalls094.accNew env
 c11:=fun obs phase=>match obs with | none=>ok () | some f=>f phase

theorem zero_array :
 arr toT3 (Array.repeat 29#usize (fromT3 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO))=
 LIB_Instances.VL.zeroE29 := by
 apply Subtype.ext
 change List.map toT3 (List.replicate 29 (fromT3 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO))=
  List.replicate 29 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO
 rw [List.map_replicate,fromT3_inverse]
#print axioms zero_array
end AspisR1.NNG_ConcreteCalls094
