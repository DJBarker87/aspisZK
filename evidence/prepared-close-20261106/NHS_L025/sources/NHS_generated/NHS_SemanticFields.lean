import NHS_FinishFields
import NHS_Fields
import RPz7_SAP_CircleCanonical
import RPz7_PAln_CircleCalls
import RPz7_SemanticRoundAlphaSelectedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_SemanticFields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The primitive semantic/circle producer supplies the checkpoint's copied
fields. The actual circle dictionary is fixed, rather than arbitrary B.circle. -/
theorem source (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
 {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
 (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
 (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (sem : r1_semantic.Verified H)
 (call : FinishModel.finish R (F3M_CircleSource.install B) D pub pre before challenges obs=ok (.Ok sem)) :
 (∀ q∈sem.alpha.val,NHS_Fields.QCanonical q) ∧
 (∀ z∈sem.z.val,NHS_Fields.QCanonical z.x ∧ NHS_Fields.QCanonical z.y) := by
 obtain ⟨running,t25,t26,t27,r25,r26,z0,z1,rounds,read25,circle25,read26,circle26,points⟩ :=
   NHS_FinishFields.source R _ D pub pre before challenges obs sem call
 have alpha := SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
   R D pre before t25 running sem.alpha rounds
 have row25 := (SourceFull25.validated_record_bytes pre 25#u8 r25 read25).1
 have row26 := (SourceFull25.validated_record_bytes pre 26#u8 r26 read26).1
 obtain ⟨block0,_,call0⟩ := PAln_CircleCalls.circle25_success _ D t25 t26 r25 z0 row25 circle25
 obtain ⟨block1,_,call1⟩ := PAln_CircleCalls.circle26_success _ D t26 t27 r26 z1 row26 circle26
 have c0 := SAP_CircleCanonical.source block0 .First z0 call0
 have c1 := SAP_CircleCanonical.source block1 .Second z1 call1
 constructor
 · intro q member
   obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp member
   have bound : i<10 := by have size:=sem.alpha.property;change sem.alpha.val.length=10 at size;omega
   have h := alpha ⟨i,bound⟩
   subst q
   exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩
 · intro z member
   rw [points] at member
   change z∈[z0,z1] at member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with h|h
   · rw [h];exact c0
   · rw [h];exact c1
#print axioms source
end AspisR1.NHS_SemanticFields
