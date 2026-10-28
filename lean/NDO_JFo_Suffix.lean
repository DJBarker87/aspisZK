import RPt_JFo_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Suffix
open Aeneas Aeneas.Std Result AspisR1Stage2

def initial : alloc.vec.Vec aspis_core.field.QM31 :=
  ⟨List.replicate 64 ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,by simp;scalar_tac⟩

theorem allocated : CheckpointBytes3Allocation.filled true 64#usize
    (⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ : aspis_core.field.QM31)=ok (.Ok initial) := by
  rw [CheckpointBytes3Allocation.filled_exact]
  rfl

theorem source : T2Nat_ReaderSuffix.normalized (CheckpointBytes4Ops.ops true)
    JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize JFq_State.value JFq_Root0.value JFq_Root1.value
    JFq_Gamma.scalar JFq_Kappa.scalar JFq_Alpha0.scalar JFq_Alpha1.scalar JFq_Rho.scalar
    JFq_Queries.value JFq_Semantic.value (JFq_Raw.reader 568#usize)=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  have cursor : UScalar.cast .Usize 10#u8 = 10#usize := by scalar_tac
  have restored:=JFo_Weights.source initial (by simp only [initial,List.length_replicate])
  have step0 := JFq_Z0.source
  have step1 := JFq_Z1.source
  have step2 := JFq_Z2.source
  have step3 := JFq_Z3.source
  have step4 := JFq_Claim.source
  have step5 := JFq_Rhs.source
  have step6 := JFq_Power.source
  simp only [T2Nat_ReaderSuffix.normalized,T2Nat_Try.withRead,T2Nat_Try.withOk,
    CheckpointBytes4Ops.ops,step0,step1,step2,step3,
    step4,step5,step6,
    CheckpointBytes4Ops.finalLen,CheckpointBytes4Ops.zeroK,allocated,
    bind_tc_ok,Aeneas.Std.uncurry]
  dsimp only [JFq_Raw.reader]
  rw [restored]
  simp only [bind_tc_ok,bne_self_eq_false,Bool.false_eq_true,ite_false,cursor,lift]
  rfl

#print axioms allocated
#print axioms source
end AspisR1.JFo_Suffix
end
