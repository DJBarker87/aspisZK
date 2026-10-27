import XRn_PreparedAssociation
open Aeneas Aeneas.Std Result
open XRk_Release XRn_Carriers
set_option autoImplicit false
namespace XRn_ClaimAssociation
/-- The opaque leaf model uses the six scalar rows, not the transcript/digest
carrier. This does not prove the native arithmetic P6 bridge. -/
def rehash {H J : Type} (sem : r1_semantic.Verified H) (transcript : r1_wire.SemanticTranscript J) :
 r1_semantic.Verified J :=
 ⟨sem.roots,sem.challenges,sem.alpha,sem.claims,sem.extra,sem.before_z1,
  sem.state_before_z0,sem.z,transcript⟩

theorem part_rehash {H J : Type} (sem : r1_semantic.Verified H)
 (transcript : r1_wire.SemanticTranscript J) (y1 : Slice U8) (g : Array C.E 29#usize) (point : Nat) :
 XRk_preparedPart (rehash sem transcript) y1 g point=XRk_preparedPart sem y1 g point := rfl

theorem digest_irrelevant {H : Type} (D D' : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : C.E)
 (g : Array C.E 29#usize) (kappa : C.E) :
 verifier.prepared_claim D sem y1 inactive g kappa=verifier.prepared_claim D' sem y1 inactive g kappa := rfl

theorem rehash_result {H J : Type} (D : aspis_core.digest.Digest32 H) (D' : aspis_core.digest.Digest32 J)
 (sem : r1_semantic.Verified H) (transcript : r1_wire.SemanticTranscript J)
 (y1 : Slice U8) (inactive : C.E) (g : Array C.E 29#usize) (kappa : C.E) :
 verifier.prepared_claim D' (rehash sem transcript) y1 inactive g kappa=
 verifier.prepared_claim D sem y1 inactive g kappa := by
 unfold verifier.prepared_claim
 simp only [part_rehash]

#print axioms part_rehash
#print axioms digest_irrelevant
#print axioms rehash_result
end XRn_ClaimAssociation
