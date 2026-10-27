import Tx2N_Reader
import Tx2I_Cuts
import Port5Q1_GeometryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Execution
open Aeneas Aeneas.Std Result VTop_Stages

def control {CoreError : Type} (base : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geometry : Port3_NativeGeometryBody.Ops CoreError) : Ops :=
  {Tx2N_Install.inner base reserved query with
    op10 := Port3_NativePendingInstall.source reserved
    op11 := Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometry)
    op16 := ok 10#usize}

attribute [local irreducible] Tx2I_Cuts.tail

/-- The actual calls, not caller-chosen output equations. -/
theorem common {CoreError Hash : Type} (base : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geometryOps : Port3_NativeGeometryBody.Ops CoreError)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (pub proof checkpoint : Slice U8)
    (accepted : verifier.candidate.tx2_common (control base reserved query geometryOps)
      D pub proof checkpoint hash none = ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (saved : verifier.Accumulator)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator) (after : verifier.BatchedWeights)
      (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
      (v : verifier.View),
      Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash = ok (.Ok (p,saved)) ∧
      saved.next = 10#usize ∧
      Tx2N_Powers.powers 29#usize p.gamma = ok g ∧
      Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometryOps)
        p.queries saved.next 22#usize = ok (.Ok geometry) ∧
      Port3_NativePendingInstall.source reserved saved.weights.deref = ok (.Ok pending) ∧
      Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query))
        proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      Port3_FlushInstall.flush after returned.weights.deref = ok flushed ∧
      (control base reserved query geometryOps).op19 v p {returned with weights := back flushed}
        none = ok (.Ok ()) := by
  rw [← Tx2I_Cuts.common_source] at accepted
  unfold Tx2I_Cuts.common at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    obtain ⟨flushed,back,v,hd,hf,hfinish⟩ := Tx2I_Cuts.tail_reached _ proof _ none _ _ _ _ _ accepted
    refine ⟨_,_,_,_,_,_,_,flushed,back,v,by assumption,?_,by assumption,by assumption,
      by assumption,by assumption,hd,hf,hfinish⟩
    simp_all only [control,Tx2N_Install.inner,beq_iff_eq, bne_iff_ne, ne_eq, not_not]

#print axioms common
end AspisR1.Tx2N_Execution
end
