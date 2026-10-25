import PSem_Values
import PSem_SourceCuts
import S1ValuesOwnedPrepareViewY1V1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PSem_Y1
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft

/-- The opening gamma message comes from the same accepted preparation and
is exactly the frozen expansion of the physical Y1 region. -/
theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (semantic : Slice U8) (view : verifier.View),
      sourceView proof semantic view.y1=ok (.Ok view) ∧
      bytesOf view.y1.val=expand 29 (slice (bytesOf proof.val) 7031 464) ∧
      view.y1.length=928 ∧
      ∀ l : Usize, l.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
        AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok value ∧
        AspisR1CurrentPreparedClaim.Concrete.Canonical value := by
  obtain ⟨stored,initial,semantic,view,sem,read,expanded,storedLength,initialLength,y1Length,
    formula,wide,verify,prepare,fields⟩ := prepare_view_y1
      (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo)))
      AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
      D pub proof hash run.p (Array.repeat 29#usize run.zero) run.scratch run.prepare_call
  have bytes := PSem_Values.source_expansion stored initial view.y1 expanded
  have physical := PSem_Slices.range_bytes proof stored 7031#usize 7495#usize read
  change stored.val=(proof.val.drop 7031).take 464 at physical
  have region : bytesOf stored.val=slice (bytesOf proof.val) 7031 464 := by
    rw [physical]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  rw [region] at bytes
  have count : stored.length/16=29 := by rw [storedLength]
  rw [count] at bytes
  exact ⟨semantic,view,wide,bytes,y1Length,fields⟩

#print axioms on_run
end AspisR1.PSem_Y1
end
