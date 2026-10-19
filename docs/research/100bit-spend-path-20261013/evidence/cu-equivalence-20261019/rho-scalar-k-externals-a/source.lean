import AspisR1RhoScalarK.Types
import AspisR1RhoDiagnostics.Funs
import ExtractedQM31SamplerCorrect

/-! The shared block operation is arbitrary, not assumed successful. The
sampler and diagnostic constructors bind to their checked exact source.
-/
namespace AspisR1CuRho
open Aeneas Aeneas.Std Result
class ScalarKBlocks where
  block : {H : Type} → Digest32 H → transcript.Transcript H → U8 → Slice U8 →
    Result (Array U8 32#usize × transcript.Transcript H)
abbrev transcript.Transcript.block [ScalarKBlocks] := @ScalarKBlocks.block _

def sampler.fromSource (q : AspisR1Qm31SamplerIndex.field.QM31) : field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def sampler.qm31_sample (block : Array U8 32#usize) : Result field.QM31 := do
  let q ← AspisR1Qm31SamplerIndex.sampler.qm31_sample block
  .ok (sampler.fromSource q)
end AspisR1CuRho
