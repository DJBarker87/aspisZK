import S1FinishSelectorsV1
import S1ClaimAcceptedCallerRangesV1
import S1AcceptedSemanticNumericV1
import S1QueryArrayOperationsV1
set_option autoImplicit false
namespace AspisS1MaskCallerDomains
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open AspisS1ExtractedRoundChildren

/-- All four source coordinates; no polynomial/protocol hypothesis. -/
def Canonical (q : MainQM) : Prop :=
  (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
  (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)

def ClaimsCanonical {H : Type} (sem : r1_semantic.Verified H) : Prop :=
  ∀ row ∈ sem.claims.val, ∀ q ∈ row.val, Canonical q

/-- The two concrete source selectors and exact g read are normally returned
on the SAME full semantic carrier, with their actual values in range. -/
def MaskInputRanges {H : Type} (sem : r1_semantic.Verified H) : Prop :=
  ∀ D : aspis_core.Digest32 H,
  ∃ (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
    (row0 : Array MainQM 29#usize) (g : MainQM),
    AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first ∧
    AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second ∧
    Array.index_usize sem.claims 0#usize=ok row0 ∧
    Array.index_usize row0 27#usize=ok g ∧
    (∀ q ∈ first.val, Canonical q) ∧ (∀ q ∈ second.val, Canonical q) ∧
    Canonical g ∧ (∀ q ∈ sem.alpha.val, Canonical q)

/-- Complete nominal carrier map, all87 cells. The accepted checked-Q input
ranges are transported, not independently required at the source caller. -/
theorem claim_ranges_to_source {H : Type} (sem : r1_semantic.Verified H)
    (h : AspisS1ClaimAcceptedScalarRanges.ClaimsCanonical (toClaimSem sem)) :
    ClaimsCanonical sem := by
  change ∀ row ∈ sem.claims.val.map (mapArray toClaimQ),
    ∀ q ∈ row.val, AspisS1ClaimAcceptedScalarRanges.ScalarCanonical q at h
  intro row member q qmember
  have hc := h (mapArray toClaimQ row) (List.mem_map.mpr ⟨row,member,rfl⟩)
    (toClaimQ q) (List.mem_map.mpr ⟨q,qmember,rfl⟩)
  change ∀ w ∈ [q.c0.a,q.c0.b,q.c1.a,q.c1.b], w.val<2147483647 at hc
  exact ⟨⟨hc _ (by simp),hc _ (by simp)⟩,⟨hc _ (by simp),hc _ (by simp)⟩⟩

theorem cell_canonical {H : Type} (sem : r1_semantic.Verified H)
    (h : ClaimsCanonical sem) (i : Nat) :
    Canonical (AspisS1FinishSelectors.cell sem.claims i) := by
  unfold AspisS1FinishSelectors.cell
  exact h _ (List.getElem_mem _) _ (List.getElem_mem _)

/-- TOTAL selector/index preparation on the reached numeric domain. Native
Std/caller interpretation remains with its existing source boundary. -/
theorem mask_inputs {H : Type} (sem : r1_semantic.Verified H)
    (claims : ClaimsCanonical sem)
    (alpha : ∀ q ∈ sem.alpha.val, Canonical q) : MaskInputRanges sem := by
  intro D
  obtain ⟨first,hfirst,firstValues⟩ := AspisS1FinishSelectors.first_total D sem.claims
  obtain ⟨second,hsecond,secondValues⟩ := AspisS1FinishSelectors.second_total D sem.claims
  let row0 := sem.claims.val[0]'(by simpa [sem.claims.property])
  let g := row0.val[27]'(by simpa [row0.property])
  have rowCall : Array.index_usize sem.claims 0#usize=ok row0 :=
    AspisS1QueryArrayOperations.index_total sem.claims 0#usize (by scalar_tac)
  have gCall : Array.index_usize row0 27#usize=ok g :=
    AspisS1QueryArrayOperations.index_total row0 27#usize (by scalar_tac)
  refine ⟨first,second,row0,g,hfirst,hsecond,rowCall,gCall,?_,?_,?_,alpha⟩
  · intro q member
    rw [firstValues] at member
    obtain ⟨i,_,same⟩ := List.mem_map.mp member
    subst q
    exact cell_canonical sem claims i
  · intro q member
    rw [secondValues] at member
    obtain ⟨i,_,same⟩ := List.mem_map.mp member
    subst q
    exact cell_canonical sem claims (16+i)
  · exact claims row0 (List.getElem_mem _) g (List.getElem_mem _)

/-- Same successful concrete borrowed claim supplies its Claims input ranges.
The alpha ranges belong to this same semantic return. -/
theorem accepted_claim_mask_inputs {H : Type}
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive kappa out : PE) (g : Array PE 29#usize)
    (accepted : AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive g kappa=ok (.Ok out))
    (numeric : AspisS1SemanticArrayRanges.VerifiedNumeric sem) : MaskInputRanges sem := by
  have claims := claim_ranges_to_source sem
    (AspisS1ClaimAcceptedCallerRanges.borrowed_claim_cells_canonical D sem y1 inactive kappa out g accepted)
  apply mask_inputs sem claims
  intro q member
  have h := numeric.1 q member
  change Canonical q at h
  exact h

#print axioms claim_ranges_to_source
#print axioms cell_canonical
#print axioms mask_inputs
#print axioms accepted_claim_mask_inputs
end AspisS1MaskCallerDomains
