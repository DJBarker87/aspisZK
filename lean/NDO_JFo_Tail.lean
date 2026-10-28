import NDO_JFo_ScalarStage
import NDO_JFo_AuthBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Tail
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source : Port4A_NativeReader.tail (CheckpointBytes4Ops.ops true)
    JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize
    (JFq_Range.segment 1736 32 (by decide)) JFo_AuthBytes.checksum=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  rw [← T2Nat_ReaderBody.source]
  have compare:=JFq_Compare.ne _ _ JFo_AuthBytes.checksum_selected
  have step0 := JFq_State.raw
  dsimp only [JFq_Raw.reader] at step0
  have step1 := JFq_Root0.raw
  dsimp only [JFq_Raw.reader] at step1
  have step2 := JFq_Root1.raw
  dsimp only [JFq_Raw.reader] at step2
  simp only [T2Nat_ReaderBody.tail,T2Nat_ReaderPrefix.normalized,CheckpointBytes4Ops.ops,
    compare,bind_tc_ok,Bool.false_eq_true,ite_false,step0,step1,step2,
    Aeneas.Std.uncurry]
  exact JFo_ScalarStage.source

theorem native : Port4A_NativeReader.tail (T2Nat_ReaderOps.ops true)
    JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize
    (JFq_Range.segment 1736 32 (by decide)) JFo_AuthBytes.checksum=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) :=
  (T2Nat_TailJoin.source true JFx_NativeBytes.checkpoint .S2 _ _ _ _ _).mpr source

#print axioms source
#print axioms native
end AspisR1.JFo_Tail
end
