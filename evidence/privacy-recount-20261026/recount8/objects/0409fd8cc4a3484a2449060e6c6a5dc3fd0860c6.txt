import R1Z.ProverCommitPolicy23
import GammaCandidateTotalityV14
import IndexedCandidateOrdinaryRetainedBridgeV5
/-! Concrete suffix policies from retained owned sampler references. Arithmetic
success is unconditional. The external source evidence must additionally pin
both indexed traversals; these definitions assert no native history equality. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPolicies25
open Aeneas Aeneas.Std Result AspisR1SimControl21
open AspisR1GammaCaller.DigitsModel
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev OwnedE := AspisR1Post25Sampler.field.WideExact
abbrev GammaE := AspisR1GammaCaller.field.WideExact
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize

def fromOwned (v : OwnedE) : E :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def toOwned (v : E) : OwnedE :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def fromGamma (v : GammaE) : E :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def decode (v : E) :=
  AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.candidateWideToExact (toOwned v)

theorem owned_roundtrip (v : OwnedE) : toOwned (fromOwned v) = v := by cases v; rfl

def gamma (block : Bytes32) : Result E := do
  let value ← AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block
  ok (fromGamma value)
def ordinary (block : Bytes32) : Result E := do
  let value ← AspisR1Post25Sampler.sampler.ordinary_sample block
  ok (fromOwned value)

abbrev QueryPolicy := Blocks → Blocks → Result (core.result.Result
  ((Array U32 22#usize) × Bytes32) verifier.Error)

def policy (query : QueryPolicy) : transcript.control21.Policy Unit where
  gamma := gamma
  ordinary := ordinary
  qm31 := ProverCommitPolicy23.sample
  queries := query

variable (query : QueryPolicy)

/-- Gamma always returns a machine value; no block or sampler success
premise is carried by the installed policy. -/
theorem gamma_total (block : Bytes32) : ∃ value, (policy query).gamma block = ok value := by
  obtain ⟨value,h⟩ := candidate_gamma_total block
  exact ⟨fromGamma value,by simp only [policy,gamma,h,bind_tc_ok]⟩

/-- Ordinary sampling also returns its exact retained field rank on every
block, rather than only describing an assumed successful execution. -/
theorem ordinary_total (block : Bytes32) :
    ∃ value, (policy query).ordinary block = ok value ∧
      decode value = R0C.ModuloField.fieldRank
        ⟨AspisR1.SourceSamplerByteRank.rank block % AspisCircleGroupOrder.P^8,
          Nat.mod_lt _ (Nat.pow_pos (by decide))⟩ := by
  obtain ⟨value,h,meaning⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV5.ordinary_sample_candidate_eq_fieldRank block
  refine ⟨fromOwned value,?_,?_⟩
  · simp only [policy,ordinary,h,bind_tc_ok]
  · simpa only [decode,owned_roundtrip] using meaning

/-- Nominal wide-field conversion preserves the existing exact gamma
interpretation, coefficient for coefficient. -/
theorem gamma_decode (value : GammaE) : decode (fromGamma value) = gammaWideToExact value := rfl

/-- Exact gamma field rank on every input, with the finite rank's bound
inherited from the existing arithmetic theorem. -/
theorem gamma_rank (block : Bytes32) :
    ∃ value, (policy query).gamma block = ok value ∧
      ∃ scalar : Fin (AspisCircleGroupOrder.P^8),
        scalar.val = AspisR1.SourceSamplerByteRank.rank block %
          (AspisCircleGroupOrder.P^8-1)+1 ∧
        decode value = R0C.ModuloField.fieldRank scalar := by
  obtain ⟨value,h⟩ := candidate_gamma_total block
  obtain ⟨digits,hd,hcanonical,hvalue,hmeaning⟩ := candidate_gamma_decode_fieldRank block value h
  have bound : AspisR1.SourceSamplerByteRank.rank block %
      (AspisCircleGroupOrder.P^8-1)+1 < AspisCircleGroupOrder.P^8 := by
    have hbound := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
      (AspisR1.SourceSamplerByteRank.rank_lt block)).2
    rw [AspisR1.SamplerNatModel.gammaDigits_value
      (AspisR1.SourceSamplerByteRank.rank_lt block)] at hbound
    simpa [AspisR1.SamplerMachineBounds.P,AspisCircleGroupOrder.P] using hbound
  refine ⟨fromGamma value,?_,⟨_,bound⟩,rfl,?_⟩
  · simp only [policy,gamma,h,bind_tc_ok]
  · rw [gamma_decode]
    exact hmeaning

/-- After an actual block transition the installed scalar sampler always
produces a value. Allocation/cast outcomes, trace entry and full retained
state remain in the extracted continuation verbatim. -/
theorem scalar_after_block {H : Type} (hash : aspis_core.digest.Digest32 H)
    (state next : transcript.control21.Transcript H Unit)
    (row : U8) (payload : Slice U8) (nonzero : Bool) (block : Bytes32)
    (block_success : transcript.control21.Transcript.block hash (policy query)
      state row payload = ok (block,next)) :
    ∃ value, transcript.control21.Transcript.scalar hash (policy query)
      state row payload nonzero =
        (do let index ← lift (UScalar.cast .Usize row)
            let trace ← alloc.vec.Vec.push next.trace (4#u16,index,value)
            ok (value,{next with trace := trace})) := by
  cases nonzero with
  | false =>
    obtain ⟨value,h,_⟩ := ordinary_total query block
    refine ⟨value,?_⟩
    simp only [transcript.control21.Transcript.scalar,block_success,bind_tc_ok,
      Aeneas.Std.uncurry_apply_pair,Bool.false_eq_true,if_false,h]
  | true =>
    obtain ⟨value,h⟩ := gamma_total query block
    refine ⟨value,?_⟩
    simp only [transcript.control21.Transcript.scalar,block_success,bind_tc_ok,
      Aeneas.Std.uncurry_apply_pair,if_true,h]

/-- Scalar and rho callbacks are concrete. The query callback is still
explicit; this theorem does not assert its source correspondence. -/
theorem installed (blocks advances : Blocks) :
    (policy query).queries blocks advances = query blocks advances := rfl

#print axioms owned_roundtrip
#print axioms gamma_total
#print axioms ordinary_total
#print axioms gamma_decode
#print axioms gamma_rank
#print axioms scalar_after_block
#print axioms installed
end R1Z.ProverCommitPolicies25
