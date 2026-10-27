import JGq_PairPrefix
import JGq_SharedHigh
import JGq_Low
import JGo_TX2_Partial
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PairCalls
open Aeneas Aeneas.Std Result

/-- Constructed local source calls on one retained operand tuple. The first
regular-kind call in the parent remains an actual computation, not a success
hypothesis. This does not assert a complete producing Pair or accepted wrapper. -/
def Facts : Prop :=
  FIo_Native.weights.powers 4#usize JGq_Powers0.x=ok JGq_Powers0.a4 ∧
  FIo_Native.weights.powers 4#usize JGq_Powers1.x=ok JGq_Powers1.a4 ∧
  FIo_Native.weights.powers 7#usize JGq_PowersK.x=ok JGq_PowersK.a7 ∧
  FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} JGq_Common.w
    (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (JGq_Common.w,JGq_Common.a16) ∧
  FIo_Native.weights.shared_partials JGq_Partial.f JGq_Common.a16=ok (.Ok JGq_SharedPartials.value) ∧
  (∀ before,FIo_Native.weights.shared_high JGq_SharedPartials.value JGq_Common.w JGq_Powers0.a4 JGq_Powers1.a4 before=
    ok (.Ok (),JGq_SharedHigh.write before)) ∧
  FIo_Native.weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize} JGq_Powers0.a4 JGq_Powers1.a4
    (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok JGq_Low.a16 ∧
  FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
    (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=JGq_PairPrefix.adapted

theorem source : Facts :=
  ⟨JGq_Powers0.source,JGq_Powers1.source,JGq_PowersK.source,JGq_Common.source,
    JGq_SharedPartials.source,JGq_SharedHigh.source,JGq_Low.source,JGq_PairPrefix.source⟩
#print axioms source

/-- Same retained saved Vec, explicit real-hash realization, and JGo's SAME
query-returned accumulator/flush, together with the local Pair computations.
No Pair, final dot, finish or wrapper success is supplied as a premise. -/
theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {C Hash : Type} (base : VTop_Stages.Ops) (seed : AspisR1Stage2.Stage2Finish.FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JGo_TX2_Partial.LocalFacts base seed err geometry query D hash ∧ Facts := by
  have h := JGo_TX2_Partial.on_saved saved same base seed err geometry query D hash realizes
  exact ⟨h.1,h.2,source⟩
#print axioms on_saved
end AspisR1.JGq_PairCalls
end
