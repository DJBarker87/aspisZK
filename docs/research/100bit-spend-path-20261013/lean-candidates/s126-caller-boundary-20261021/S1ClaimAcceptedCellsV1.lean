import S1ClaimAcceptedScalarRangesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1ClaimAcceptedScalarRanges
open AspisR1CurrentPreparedClaim AspisR1S5ClaimDotConcreteAdapter

def ClaimsCanonical {H : Type} (sem : r1_semantic.Verified H) : Prop :=
  ∀ row ∈ sem.claims.val, ∀ scalar ∈ row.val, ScalarCanonical scalar

/-- All87 cells of the same full Claims carrier, including each row's D cell.
No successful Claims producer or input-canonicality assumption is required. -/
theorem accepted_claim_cells_canonical {H : Type} (rawFn : RawFn)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive kappa out : E) (g : Array E 29#usize)
    (accepted : verifier.prepared_claim (concreteOps rawFn) D sem y1 inactive g kappa = ok (.Ok out)) :
    ClaimsCanonical sem := by
  intro row rowMember scalar scalarMember
  obtain ⟨p,hp,hrow⟩ := List.mem_iff_getElem.mp rowMember
  obtain ⟨l,hl,hscalar⟩ := List.mem_iff_getElem.mp scalarMember
  have pointBound : p < 3 := by simpa only [sem.claims.property,show (3#usize).val=3 from rfl] using hp
  have columnBound : l < 29 := by simpa only [row.property,show (29#usize).val=29 from rfl] using hl
  let pi := Usize.ofNatCore p (by scalar_tac)
  let li := Usize.ofNatCore l (by scalar_tac)
  have pval : pi.val = p := by simp only [pi,Usize.ofNatCore_val_eq]
  have lval : li.val = l := by simp only [li,Usize.ofNatCore_val_eq]
  obtain ⟨value,read,canonical⟩ := accepted_claim_read_ranges rawFn D sem y1 inactive kappa out g accepted
    pi (by omega) li (by omega)
  have small : pi ≤ 2#usize := by
    change pi.val ≤ (2#usize).val
    simp only [show (2#usize).val=2 from rfl]
    omega
  obtain ⟨actualRow,readRow,readValue⟩ :=
    ClaimScalar.read_claims_success (concreteOps rawFn) sem y1 pi li value small read
  obtain ⟨indexedRow,indexRow,rowValue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec sem.claims pi (by simpa only [pval] using hp))
  have rowEq : actualRow = row := by
    have same := Result.ok.inj (readRow.symm.trans indexRow)
    rw [same,rowValue]
    simpa only [pval] using hrow
  rw [rowEq] at readValue
  obtain ⟨indexedValue,indexValue,scalarValue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec row li (by simpa only [lval] using hl))
  have valueEq : value = scalar := by
    have same := Result.ok.inj (readValue.symm.trans indexValue)
    rw [same,scalarValue]
    simpa only [lval] using hscalar
  simpa only [valueEq] using canonical

#print axioms accepted_claim_cells_canonical
end AspisS1ClaimAcceptedScalarRanges
