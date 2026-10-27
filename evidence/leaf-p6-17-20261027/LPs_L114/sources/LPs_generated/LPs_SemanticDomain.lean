import LPs_ClaimsDomain
import JGi_FinishFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPs_SemanticDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open LPi_FieldValues

theorem decoded (r : r1_wire.ValidatedRecord) (off : Usize)
    (a : Array aspis_core.field.QM31 29#usize)
    (call : AspisS1ExtractedRoundChildren.decodeMain 29#usize r off=ok (.Ok a)) :
    LPs_ClaimsDomain.RowCanonical a := by
  let parent : AspisR1ClaimsUnrolledParent.Record := ⟨r.row,r.framed⟩
  have same : ClaimsUnrolledFinish.toMainRecord parent=r := by cases r;rfl
  have port : ClaimsUnrolledFinish.sourceDecode 29#usize parent off=
      ok (.Ok (ClaimsUnrolledFinish.fromMainArray a)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [same,call]
  have canonical := LPs_ClaimsDomain.decoded parent off _ port
  simpa only [ClaimsUnrolledFinish.array_back] using canonical

theorem row (a : Array aspis_core.field.QM31 29#usize)
    (ha : LPs_ClaimsDomain.RowCanonical a) :
    ∀ q ∈ (mapArray toClaimQ a).val,canonQ (LPq_ReadPorts.backQ q) := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp hx
  have bound : i<29 := by have := a.property;change a.val.length=29 at this;omega
  subst x
  exact ha ⟨i,bound⟩

theorem source (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre before challenges obs=ok (.Ok sem)) :
    LPq_ReadPorts.SemCanonical (toClaimSem sem) := by
  obtain ⟨r25,r26,claims,read25,extra,read26,before⟩ := JGi_FinishFields.source
    AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))} D pub pre before challenges obs sem finish
  have cc := LPs_ClaimsDomain.claims pre sem.claims claims
  refine ⟨?_,row sem.extra (decoded _ _ _ extra),
    row sem.before_z1 (decoded _ _ _ before)⟩
  intro a ha
  obtain ⟨original,mem,rfl⟩ := List.mem_map.mp ha
  exact row original (cc original mem)

#print axioms decoded
#print axioms row
#print axioms source
end AspisR1.LPs_SemanticDomain
end
