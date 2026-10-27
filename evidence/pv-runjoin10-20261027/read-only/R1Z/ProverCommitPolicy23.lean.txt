import R1Z.ProverCommitTail21
import R1Z.ProverCommitSemanticSampler22
/-! Install the proved concrete QM31 sampler in the extracted suffix policy.
Gamma, ordinary and query policies remain visible parameters. No equality
of this owned trace with every native TLS call is inferred. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPolicy23
open Aeneas Aeneas.Std Result
open AspisR1SimControl21
abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev K := aspis_core.field.QM31
abbrev Bytes32 := Array U8 32#usize

def fromPublic (q : PublicQM) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toPublic (q : K) : PublicQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem roundtrip (q : PublicQM) : toPublic (fromPublic q) = q := by
  cases q
  rfl

def sample (block : Bytes32) : Result K := do
  let q ← AspisR1PublicPreparation.sampler.qm31_sample block
  ok (fromPublic q)

def decode (q : K) : AspisWideTower.WideExact :=
  algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact
    (AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld (toPublic q))))

def policy {P : Type} (remaining : transcript.control21.Policy P) : transcript.control21.Policy P :=
  { remaining with qm31 := sample }

/-- Concrete nominal conversion, exact machine sampling success and model
meaning. No sampler success is supplied by the caller. -/
theorem sample_total (block : Bytes32) :
    ∃ q : K, sample block = ok q ∧
      decode q = R0P.SemSource.semChal (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  obtain ⟨q,hq,meaning⟩ := ProverCommitSemanticSampler22.sample_total_semChal block
  refine ⟨fromPublic q,?_,?_⟩
  · simp only [sample,hq,bind_tc_ok]
  · simpa only [decode,roundtrip] using meaning

/-- This concrete policy really is installed in the suffix, rather than
retained as an unrelated sampler theorem. -/
theorem installed_total {P : Type} (remaining : transcript.control21.Policy P) (block : Bytes32) :
    ∃ q : K, (policy remaining).qm31 block = ok q ∧
      decode q = R0P.SemSource.semChal (AspisV8R19.SqueezeOracleBridge.decodeState block) :=
  sample_total block

/-- Row 32 executes the concrete sampler and preserves the source-shaped
state/trace actions. The embedding and Vec push are retained, including
all their failure or divergence outcomes. -/
theorem rho_caller {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (remaining : transcript.control21.Policy P)
    (state : transcript.control21.Transcript H P) (row : U8) (payload : Slice U8) :
    transcript.control21.Transcript.scalar_k hash (policy remaining) state row payload =
      (do
        let (block,next) ← transcript.control21.Transcript.block hash (policy remaining) state row payload
        let q ← sample block
        let index ← lift (UScalar.cast .Usize row)
        let embedded ← aspis_core.field.wide_exact.WideExact.from_qm31 q
        let trace ← alloc.vec.Vec.push next.trace (4#u16,index,embedded)
        ok (q,{next with trace := trace})) := rfl

/-- Every successful block call supplies the concrete rho and its model
meaning. Later embedding/allocation failures are preserved verbatim. -/
theorem rho_after_block {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (remaining : transcript.control21.Policy P)
    (state next : transcript.control21.Transcript H P) (row : U8) (payload : Slice U8)
    (block : Bytes32)
    (block_success : transcript.control21.Transcript.block hash (policy remaining) state row payload =
      ok (block,next)) :
    ∃ q : K, decode q = R0P.SemSource.semChal
        (AspisV8R19.SqueezeOracleBridge.decodeState block) ∧
      transcript.control21.Transcript.scalar_k hash (policy remaining) state row payload =
        (do
          let index ← lift (UScalar.cast .Usize row)
          let embedded ← aspis_core.field.wide_exact.WideExact.from_qm31 q
          let trace ← alloc.vec.Vec.push next.trace (4#u16,index,embedded)
          ok (q,{next with trace := trace})) := by
  obtain ⟨q,hq,meaning⟩ := sample_total block
  refine ⟨q,meaning,?_⟩
  rw [rho_caller]
  simp only [block_success,bind_tc_ok,Aeneas.Std.uncurry_apply_pair,hq]

#print axioms rho_after_block
#print axioms roundtrip
#print axioms sample_total
#print axioms installed_total
#print axioms rho_caller
end R1Z.ProverCommitPolicy23
