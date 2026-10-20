import Stage2QueryChecks
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.Stage2Finish

/-- Exact first-fact conclusions; these do not authenticate checkpoint provenance
or imply a literal matching-data reader. -/
structure ShapeDigestFacts {H : Type} (digestInst : aspis_core.digest.Digest32 H)
    (checkpoint proof : Slice U8) (hash : H) : Prop where
  length : ∃ size, AspisR1Stage2ContinuationParse.compact.PROOF_BYTES = ok size ∧
    Slice.len proof = size
  digest : ∃ (stored : Slice U8) (chunks : Slice (Slice U8)) (value : Array U8 32#usize),
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      checkpoint { start := 16#usize, «end» := 48#usize } = ok stored ∧
    lift (Array.to_slice (Array.make 1#usize [proof])) = ok chunks ∧
    digestInst.digest hash chunks = ok value ∧ stored.val = value.val

/-- The same proof bytes feed the successful shape parser and checkpoint rehash.
The source S2 route is chosen explicitly rather than a free variant cast. -/
theorem shape_digest_facts
    (parseOps : AspisR1Stage2ContinuationParse.ParseShapeOps) (resumeOps : ResumeOps)
    {H : Type} (digestInst : aspis_core.digest.Digest32 H)
    (compare : ∀ (s : Slice U8) (a : Array U8 32#usize),
      resumeOps.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (checkpoint proof publicBytes : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (parsed : AspisR1Stage2ContinuationParse.verifier.candidate.parse_shape parseOps proof =
      ok (.Ok .S2))
    (resumed : verifier.resumeWithOps resumeOps digestInst checkpoint proof publicBytes .S2 hash =
      ok (.Ok (p,a))) : ShapeDigestFacts digestInst checkpoint proof hash := by
  exact ⟨AspisR1Stage2ContinuationParse.successful_length parseOps proof .S2 parsed,
    resume_rehash_checkpoint_field resumeOps digestInst compare checkpoint proof publicBytes .S2 hash p a resumed⟩

#print axioms shape_digest_facts
end AspisR1Stage2.Stage2Finish
