import FJo_Tx1AlphaSource
import FJo_AlphaIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Tx1AlphaCanonical
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- The actual first-alpha operand is canonical by its installed constructor. -/
theorem value {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (alpha : AspisR1Stage2.Stage2Finish.E)
    (read : Array.index_usize (Tx1Q_Carriers.prepared run.p).alpha 0#usize=ok alpha) :
    OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE alpha) := by
  obtain ⟨p,rs,output,scratch,a,b,array,h,hb⟩ := FJo_Tx1AlphaSource.value ops reserved query geo B std D hash pub publicBytes proof split saved run
  rw [←output] at read
  have cell := FJc_ReadSlot.slot _ _ _ read
  change (p.alpha.val.map currentE |>.map Tx1Q_Carriers.e)[0]?=some alpha at cell
  rw [array] at cell
  have same : Tx1Q_Carriers.e (currentE a)=alpha := by
    simpa only [Array.make,List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.some.injEq] using cell
  rw [←same]
  exact ⟨⟨h.1.1.1,h.1.1.2,h.1.2.1,h.1.2.2⟩,⟨h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2⟩⟩
#print axioms value
end AspisR1.FJo_Tx1AlphaCanonical
end
