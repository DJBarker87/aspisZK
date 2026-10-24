import S1PreparedPowersCallbacksV1
import S1PowersCanonicalInjectiveV1
import S1QueryArrayOperationsV1
set_option autoImplicit false
namespace AspisS1PreparedPowersCallbacks
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisS1TopPrepareCarrier AspisS1TopPowers AspisS1PowersCallbackChain
open AspisR1PowersConcreteMul AspisR1PowersExactProduct

/-- SAME successful preparation and SAME scratch, all eight words per entry.
The complete original callback sequence executes 29 multiplications, retains
its last poststate, and returns exactly the reused caller scratch values.
Kappa's seven callbacks are TOTAL on the same call-derived seed as well.
This does not assert native Std/from_fn or whole SDK correspondence. -/
theorem prepared_scratch_callbacks (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (success : AspisS1TopPrepareSource.prepare ops D pub proof hash none input=
      ok (.Ok prepared,scratch)) :
    ∃ last,
      execute 29#usize (one,callbackE prepared.gamma) (slots 29#usize)=
        ok (scratch.val.map callbackE,(last,callbackE prepared.gamma)) ∧
      Canonical last ∧ decode last=decode (callbackE prepared.gamma)^29 ∧
      Complete 7#usize (callbackE prepared.kappa) := by
  obtain ⟨gammaComplete,kappaComplete⟩ :=
    prepared_complete ops D pub proof hash input scratch prepared success
  obtain ⟨values,last,run,len,canonicalLast,decodedLast,cells⟩ := gammaComplete
  have length : values.length=29 := len
  have same : values=scratch.val.map callbackE := by
    apply List.ext_getElem
    · simp only [List.length_map,scratch.property]
      exact length
    · intro j hj hs
      have bound : j<29 := by omega
      let i : Usize := slot 29#usize ⟨j,bound⟩
      have index : i.val=j := slot_val _ _
      have indexBound : i.val<29 := by omega
      obtain ⟨value,read,hcanonical,hdecode⟩ :=
        AspisS1TopPrepareSource.prepare_scratch_exact ops D pub proof hash input scratch prepared success i indexBound
      have readActual := AspisS1QueryArrayOperations.index_total (mapArray claimE scratch) i indexBound
      have valueEq : value=claimE (scratch.val[j]'(by simpa only [List.length_map] using hs)) := by
        have eq := Result.ok.inj (read.symm.trans readActual)
        simpa only [mapArray,List.getElem_map,index] using eq
      have rawCanonical : Canonical (callbackE (scratch.val[j]'(by simpa only [List.length_map] using hs))) := by
        apply canonical
        rw [←valueEq]
        exact hcanonical
      have rawDecode : decode (callbackE (scratch.val[j]'(by simpa only [List.length_map] using hs)))=
          decode (callbackE prepared.gamma)^j := by
        change AspisR1CurrentPreparedClaim.Concrete.decode (claimE (scratch.val[j]'_))=
          AspisR1CurrentPreparedClaim.Concrete.decode (claimE prepared.gamma)^j
        rw [←valueEq]
        simpa only [index] using hdecode
      simp only [List.getElem_map]
      exact canonical_injective _ _ (cells j hj).1 rawCanonical ((cells j hj).2.trans rawDecode.symm)
  refine ⟨last,?_,canonicalLast,decodedLast,kappaComplete⟩
  simpa only [same] using run

#print axioms prepared_scratch_callbacks
end AspisS1PreparedPowersCallbacks
