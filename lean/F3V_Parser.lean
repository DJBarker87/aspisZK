import F3V_FirstSlots
import Op4P_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Parser
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisR1CurrentCaller

theorem accepted {C Hash : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (success : verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base ops reserved query geo) B std)
      D semantic pub proof 10#usize hash none=ok (.Ok saved)) :
    OraclePortHeader.accepts (bytesOf proof.val)=true ∧
      OraclePortCompactDraft.scan (bytesOf proof.val) := by
  obtain ⟨_,variant,zero,p,scratch,shape,scan,_⟩ := Tx1Reachability.tx1_success _ _ _ pub proof 10#usize hash saved success
  have headerCall : Op3I_Install.sourceBody proof=ok (.Ok variant) := shape
  have header := (Op3I_Install.header_of_success proof variant headerCall).2
  have length : proof.val.length=57607 := by
    simpa only [bytesOf,List.length_map] using ((OraclePortHeader.accepts_iff _).mp header).1
  have scanCall : Op4P_Install.sourceBody proof=ok (.Ok ()) := scan
  exact ⟨header,Op4P_Install.scan_of_success proof length scanCall⟩

#print axioms accepted
end AspisR1.F3V_Parser
end
