import R1Z.PV_RunJoin_TranscriptReseed51
import R1Z.PV_RunJoin_ScalarSuccessModel50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TranscriptHash51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem reseed (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : aspis_core.digest.LegacyHashFn) (semantic : Array U8 32#usize) (v : transport.Variant)
    (out : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (h : @host_transcript.Transcript.new (types base) (selected base heap box ops) _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
      hash semantic v=ok out) : out.hash=hash := by
  rw [PV_RunJoin_TranscriptReseed51.source] at h
  obtain ⟨state,hs,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  have eq := Result.ok.inj h
  cases eq
  rfl

theorem block [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_transcript.Transcript H) (row : U8) (payload : Slice U8) (b : Array U8 32#usize)
    (h : host_transcript.Transcript.block D t row payload=ok (b,next)) : next.hash=t.hash := by
  obtain ⟨absorbed,advanced,ha,hb,had,eq⟩ := PV_RunJoin_TranscriptBlock51.reach D t next row payload b h
  rw [eq]

theorem scalar (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (t next : host_transcript.Transcript H)
    (i : Fin 4) (row : U8) (payload : Slice U8) (a : aspis_core.field.wide_exact.WideExact)
    (h : @host_transcript.Transcript.scalar (types base) (selected base heap box ops) H D
      t row payload (PV_RunJoin_SamplerValueModel50.nonzero i)=ok (a,next)) : next.hash=t.hash := by
  obtain ⟨b,raw,hb,hc,hs,hm⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops D t i row payload a next h
  exact block D t next row payload b hb
#print axioms reseed
#print axioms block
#print axioms scalar
end R1Z.PV_RunJoin_TranscriptHash51
