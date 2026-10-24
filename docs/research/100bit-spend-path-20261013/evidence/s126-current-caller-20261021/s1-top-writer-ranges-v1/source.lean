import S1TopWriterVariantV1
import S1TopPrepareRangesV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareSource
open Aeneas Aeneas.Std Result
open VTop_Stages
open AspisS1TopPrepareCarrier AspisS1TopPowers AspisR1ClaimPreparedBridge
variable {CoreError W : Type}

/-- The enclosing writer execution supplies canonical challenge fields and
its exact returned 29-cell gamma scratch. No separately successful preparation,
powers operation, chosen scratch or range hypothesis remains. -/
theorem writer_ranges (base : Ops) (sourceOps : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (batch : AspisR1.Port3_NativeBatchBody.Ops)
    (geometry : AspisR1.Port3_NativeGeometryBody.Ops CoreError)
    (query : AspisR1.Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : AspisR1.VTop_Provenance.WriterPrefix
      (AspisR1.Port3_NativeWriterShape.installed (install base sourceOps) reserved batch geometry query finish)
      D hash semantic proof split none p a) :
    p.variant=.S2 ∧ ∃ zero g,
      base.op1=ok zero ∧
      prepare sourceOps D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) ∧
      (AspisR1CurrentPreparedClaim.Concrete.Canonical (claimE p.gamma) ∧
       AspisR1CurrentPreparedClaim.Concrete.Canonical (claimE p.kappa)) ∧
      (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
        Array.index_usize (mapArray claimE g) i=ok value ∧
        AspisR1CurrentPreparedClaim.Concrete.Canonical value ∧
        AspisR1CurrentPreparedClaim.Concrete.decode value=
          AspisR1CurrentPreparedClaim.Concrete.decode (claimE p.gamma)^i.val) := by
  obtain ⟨zero,g,hzero,source⟩ := AspisR1.Port4A_PrepareCut.returned
    (install base sourceOps) reserved batch geometry query finish D hash semantic proof split p a reached
  exact ⟨writer_variant base sourceOps reserved batch geometry query finish D hash semantic proof split p a reached,
    zero,g,hzero,source,
    prepare_gamma_kappa_canonical sourceOps D semantic proof hash (Array.repeat 29#usize zero) g p source,
    prepare_scratch_exact sourceOps D semantic proof hash (Array.repeat 29#usize zero) g p source⟩

#print axioms writer_ranges
end AspisS1TopPrepareSource
