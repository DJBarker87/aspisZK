import JFq_Sem00
import JFq_Sem01
import JFq_Sem02
import JFq_Sem03
import JFq_Sem04
import JFq_Sem05
import JFq_Sem06
import JFq_Sem07
import JFq_Sem08
import JFq_Sem09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Semantic
open Aeneas Aeneas.Std Result AspisR1Stage2

def value : Array aspis_core.field.QM31 10#usize := Array.make 10#usize
  [JFq_Sem00.scalar,JFq_Sem01.scalar,JFq_Sem02.scalar,JFq_Sem03.scalar,JFq_Sem04.scalar,
   JFq_Sem05.scalar,JFq_Sem06.scalar,JFq_Sem07.scalar,JFq_Sem08.scalar,JFq_Sem09.scalar]

theorem source : CheckpointBytes4Ops.readSemanticAlpha JFx_NativeBytes.checkpoint 408#usize=
    ok (.Ok (value,568#usize)) := by
  have step0 := JFq_Sem00.source
  dsimp only [JFq_Raw.reader] at step0
  have step1 := JFq_Sem01.source
  dsimp only [JFq_Raw.reader] at step1
  have step2 := JFq_Sem02.source
  dsimp only [JFq_Raw.reader] at step2
  have step3 := JFq_Sem03.source
  dsimp only [JFq_Raw.reader] at step3
  have step4 := JFq_Sem04.source
  dsimp only [JFq_Raw.reader] at step4
  have step5 := JFq_Sem05.source
  dsimp only [JFq_Raw.reader] at step5
  have step6 := JFq_Sem06.source
  dsimp only [JFq_Raw.reader] at step6
  have step7 := JFq_Sem07.source
  dsimp only [JFq_Raw.reader] at step7
  have step8 := JFq_Sem08.source
  dsimp only [JFq_Raw.reader] at step8
  have step9 := JFq_Sem09.source
  dsimp only [JFq_Raw.reader] at step9
  simp only [CheckpointBytes4Ops.readSemanticAlpha,CheckpointBytes4Ops.semanticUsing,
    CheckpointBytes4Ops.withK,step0,step1,step2,
    step3,step4,step5,step6,
    step7,step8,step9,bind_tc_ok,Aeneas.Std.uncurry]
  rfl

theorem native : (T2Nat_ReaderOps.ops true).readSemanticAlpha JFx_NativeBytes.checkpoint 408#usize=
    ok (.Ok (value,568#usize)) :=
  (T2Nat_ReaderOps.semantic true JFx_NativeBytes.checkpoint 408#usize _).mpr source

#print axioms source
#print axioms native
end AspisR1.JFq_Semantic
end
