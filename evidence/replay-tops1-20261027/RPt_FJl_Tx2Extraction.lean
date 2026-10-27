import RPt_FJl_LoopExtraction
import RPz7_Tx2N_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_Tx2Extraction
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- The twelve resumed calls and the selected powers come from inversion of
one accepted TX2 common body. No family of successful calls is supplied. -/
theorem reached {C Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (accepted : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control base reserved query geo) D pub proof checkpoint hash none=ok (.Ok ())) :
    ∃ p saved g geometry,
      Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash=ok (.Ok (p,saved)) ∧
      saved.next=10#usize ∧ Tx2N_Powers.powers 29#usize p.gamma=ok g ∧
      ∀ j : Fin 12, ∃ a0 a1 b0 b1, a0.next.val=10+j.val ∧
        Port3_NativeQueryBody.verifier.candidate.query_values
          (Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install query)))
          proof p a0 g none geometry b0=ok (.Ok (a1,b1)) := by
  obtain ⟨p,saved,g,geometry,pending,out,after,flushed,back,v,hr,hn,hg,hgeo,hpending,hq,rest⟩ :=
    Tx2N_Execution.common base reserved query geo D hash pub proof checkpoint accepted
  refine ⟨p,saved,g,geometry,hr,hn,hg,?_⟩
  intro j
  exact FJl_LoopExtraction.installed _ proof p saved out g geometry pending after 22#usize
    (by rw [hn]; decide) hq (10+j.val) (by rw [hn]; change 10≤10+j.val; omega)
    (by have := j.isLt; change 10+j.val<22; omega)
#print axioms reached
end AspisR1.FJl_Tx2Extraction
end
