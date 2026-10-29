import R1Z.PV_RunJoin_ByteArrayList51
import R1Z.PV_RunJoin_TranscriptReseedSource51
import R1Z.PV_RunJoin_TranscriptTag51
import R1Z.PV_RunJoin_TranscriptFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TranscriptReseed51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_TranscriptRequests51 (Block)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem source (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : aspis_core.digest.LegacyHashFn) (semantic : Block) (v : transport.Variant) :
    @host_transcript.Transcript.new (types base) (selected base heap box ops) _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
      hash semantic v=(do
        let state ← hash (PV_RunJoin_TranscriptReseedSource51.request semantic (ProverRwOuterTag.byte v))
        ok ⟨state,hash⟩) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_TranscriptReseedSource51.source]
  change (do let tag ← (selected base heap box ops).op234 v
             let state ← (selected base heap box ops).op39 hash
               (PV_RunJoin_TranscriptReseedSource51.request semantic tag)
             ok (host_transcript.Transcript.mk state hash))=_
  rw [PV_RunJoin_TranscriptTag51.installed]
  simp only [bind_tc_ok,PV_RunJoin_TranscriptDigest51.installed]

theorem domain_bytes : PV_RunJoin_TranscriptReseedSource51.domain.val.map ProverCommitOwnerBytes42.byte=
    TranscriptR1.openDomain := by
  change _ = "UNPROVED:R1:PRIVATE-SALTED:P3".toByteArray.toList
  rw [←String.utf8Encode_toList]
  simp [PV_RunJoin_TranscriptReseedSource51.domain,List.utf8Encode,String.utf8EncodeChar,
    Array.to_slice,Array.make,ProverCommitOwnerBytes42.byte,
    PV_RunJoin_ByteArrayList51.of_list]

theorem frame (s : Block) (tag : U8) :
    ProverRwOuterFrames.flatten (PV_RunJoin_TranscriptReseedSource51.request s tag)=
      TranscriptR1.openDomain++[ProverCommitOwnerBytes42.byte tag]++s.val.map ProverCommitOwnerBytes42.byte := by
  simp only [ProverRwOuterFrames.flatten,PV_RunJoin_TranscriptReseedSource51.request,
    Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_append,List.map_cons,List.map_nil,domain_bytes,List.append_assoc]
#print axioms source
#print axioms domain_bytes
#print axioms frame
end R1Z.PV_RunJoin_TranscriptReseed51
