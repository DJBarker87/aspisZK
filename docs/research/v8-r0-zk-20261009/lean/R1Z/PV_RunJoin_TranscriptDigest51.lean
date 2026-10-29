import R1Z.PV_RunJoin_TranscriptBlock51
import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TranscriptDigest51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate [ExternalTypes] (ops : ExternalFuns) (hash : aspis_core.digest.LegacyHashFn)
    (parts : Slice (Slice U8)) : (ProverRwP6BodyCandidate.selected ops).op39 hash parts=hash parts := rfl
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem installed (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : aspis_core.digest.LegacyHashFn) (parts : Slice (Slice U8)) :
    (selected base heap box ops).op39 hash parts=hash parts := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_39]
  exact @candidate (types base) ops hash parts

theorem block (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (t : host_transcript.Transcript aspis_core.digest.LegacyHashFn) (row : U8) (payload : Slice U8) :
    @host_transcript.Transcript.block _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops)) t row payload=(do
      let absorbed ← t.hash (PV_RunJoin_TranscriptAbsorb51.request t.state row payload)
      let b ← t.hash (PV_RunJoin_TranscriptRequests51.message absorbed 1#u8)
      let advanced ← t.hash (PV_RunJoin_TranscriptRequests51.message absorbed 2#u8)
      ok (b,{t with state:=advanced})) := by
  rw [PV_RunJoin_TranscriptBlock51.source]
  simp only [aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32,installed]
#print axioms candidate
#print axioms installed
#print axioms block
end R1Z.PV_RunJoin_TranscriptDigest51
