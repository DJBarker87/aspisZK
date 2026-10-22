import S4Tx2PowersQuerySourceCutV1
import S4P6PowersQueryJoinV1
import S4CandidateLoopActualCallsV1
import Stage2ContinuationResumeBody
import S4V10CandidateQueryFieldEvidenceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx2ResumeTwelveFieldEvidenceV2
open AspisR1Stage2
open AspisR1FastDotsTx2PowersQuerySourceCutV1
open AspisR1S4P6PowersQueryJoinV1
open AspisR1S4CandidateLoopActualCallsV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1 (CandidateQueryFieldEvidence candidate_query_success_field_evidence)

abbrev ClaimOps := AspisR1S4P6PowersQueryJoinV1.ClaimOps
abbrev Prepared := AspisR1Stage2.verifier.Prepared
abbrev Accumulator := AspisR1Stage2.verifier.Accumulator
abbrev BatchWeights := AspisR1Stage2.verifier.BatchedWeights
abbrev ResumeValue := core.result.Result (Prepared × Accumulator) AspisR1Stage2.verifier.Error
abbrev QueryState := AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryState

/-- The tx2 continuation suffix after `resume`: preserve the source's inner
    Result branch, split guard, then the unchanged powers-through-query prefix.
    A successful inner query result therefore itself witnesses that resume
    returned a state satisfying the source split guard. -/
def tx2AfterResume {H : Type}
    (resumeResult : Result ResumeValue)
    (ops : ClaimOps H) (call : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall) (proof : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    Result (core.result.Result QueryState verifier.Error) := do
  let resumed ← resumeResult
  match resumed with
  | core.result.Result.Err e => .ok (.Err e)
  | core.result.Result.Ok (p,a) =>
      if a.next != 10#usize then .ok (.Err verifier.Error.Checkpoint)
      else do
        let q ← tx2QueryPrefix (withSourceP6WeightsPowers ops) call proof p a hash obs
        .ok (.Ok q)

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- Successful source suffix inversion: the resume output and `next=10` are
    recovered from the same success that reaches the query prefix. -/
theorem tx2_after_resume_success_inv {H : Type}
    (resumeResult : Result ResumeValue) (ops : ClaimOps H)
    (call : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall) (proof : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (out : Accumulator) (bout : BatchWeights)
    (h : tx2AfterResume resumeResult ops call proof hash obs =
      .ok (.Ok (.Ok (out,bout)))) :
    ∃ p a, resumeResult = .ok (.Ok (p,a)) ∧ a.next.val=10 ∧
      tx2QueryPrefix (withSourceP6WeightsPowers ops) call proof p a hash obs =
        .ok (.Ok (out,bout)) := by
  cases hr : resumeResult with
  | fail e => simp [tx2AfterResume, hr] at h
  | div => simp [tx2AfterResume, hr] at h
  | ok resumed =>
    cases resumed with
    | Err e => simp [tx2AfterResume, hr] at h
    | Ok pair =>
      rcases pair with ⟨p,a⟩
      by_cases hnext : a.next.val=10
      · have hprefix := h
        simp [tx2AfterResume, hr, hnext] at hprefix
        exact ⟨p,a,rfl,hnext,hprefix⟩
      · simp [tx2AfterResume, hr, hnext] at h

/-- The resumed tx2 branch yields same-array powers, start=10, and an actual
    candidate callback success plus scanned field evidence for each of its
    twelve reached query states. Strict scan and prepared canonicality remain
    explicit upstream authenticated/prepare contracts. -/
theorem tx2_after_resume_candidate_twelve_actual_fields {H : Type}
    (ops : ClaimOps H) (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (resumeResult : Result ResumeValue)
    (out : Accumulator) (bout : BatchWeights)
    (hcanonical : ∀ p a, resumeResult = .ok (.Ok (p,a)) →
      AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2AfterResume resumeResult ops
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof hash obs = .ok (.Ok (.Ok (out,bout)))) :
    ∃ p a g geometry pending claimPowers,
      resumeResult = .ok (.Ok (p,a)) ∧ a.next.val=10 ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      (withSourceP6WeightsPowers ops).makeGeometry p.queries a.next 22#usize = .ok geometry ∧
      (withSourceP6WeightsPowers ops).makePending (alloc.vec.Vec.deref a.weights) = .ok pending ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim p.gamma) = .ok claimPowers ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
        AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers ∧
      (∀ k : Fin 12, ∃ (a0 a1 : Accumulator) (b0 b1 : BatchWeights),
        a0.next.val=10+k.val ∧
        verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
          proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryFieldEvidence rest proof p a0 g claimPowers) := by
  obtain ⟨p,a,hresume,hstart,hprefix⟩ :=
    tx2_after_resume_success_inv resumeResult ops _ proof hash obs out bout h
  have hgamma := hcanonical p a hresume
  obtain ⟨g,hg,geometry,hgeometry,pending,hpending,hloop,claimPowers,hpowers,hcaller⟩ :=
    tx2_prefix_p6_powers_same_g ops
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof p a hash obs (.Ok (out,bout)) hgamma hprefix
  have hfields := candidate_twelve_queries_have_actual_call_field_results
    aops rest proof p g obs geometry a out pending bout (stage2ToClaim p.gamma)
    claimPowers hgamma hpowers hcaller hscan (by simpa using hstart) hloop
  have hcandidateFields : ∀ k : Fin 12, ∃ (a0 a1 : Accumulator) (b0 b1 : BatchWeights),
      a0.next.val=10+k.val ∧
      verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
        proof p a0 g obs geometry b0=.ok (.Ok (a1,b1)) ∧
      CandidateQueryFieldEvidence rest proof p a0 g claimPowers := by
    intro k
    obtain ⟨a0,a1,b0,b1,hindex,hcall,_hold⟩ := hfields k
    have hcandidate := candidate_query_success_field_evidence aops rest proof p a0 g
      obs geometry b0 (.Ok (a1,b1)) (stage2ToClaim p.gamma) claimPowers
      hgamma hpowers hcaller hscan hcall
    exact ⟨a0,a1,b0,b1,hindex,hcall,hcandidate⟩
  exact ⟨p,a,g,geometry,pending,claimPowers,hresume,by simpa using hstart,
    hg,hgeometry,hpending,hpowers,hcaller,hcandidateFields⟩

/-- Bind the resumed state to the selected Stage2 `resumeWithOps` body. The
    caller must still supply the selected ResumeOps backend laws; this is the
    checked continuation model, not a claim of the frozen Rust child ABI. -/
theorem resume_model_candidate_twelve_actual_field_evidence {H : Type}
    (resumeOps : AspisR1Stage2.ResumeOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (checkpoint proof public_bytes : Slice U8) (hash : H)
    (ops : ClaimOps H) (aops : AccumulateOps) (rest : QueryOps)
    (obs : Option (verifier.Phase → Result Unit))
    (out : Accumulator) (bout : BatchWeights)
    (hcanonical : ∀ p a,
      verifier.resumeWithOps resumeOps inst checkpoint proof public_bytes
        transport.Variant.S2 hash = .ok (.Ok (p,a)) →
      AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2AfterResume
      (verifier.resumeWithOps resumeOps inst checkpoint proof public_bytes
        transport.Variant.S2 hash)
      ops
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof hash obs = .ok (.Ok (.Ok (out,bout)))) :
    ∃ p a g geometry pending claimPowers,
      verifier.resumeWithOps resumeOps inst checkpoint proof public_bytes
        transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧ a.next.val=10 ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      (withSourceP6WeightsPowers ops).makeGeometry p.queries a.next 22#usize = .ok geometry ∧
      (withSourceP6WeightsPowers ops).makePending (alloc.vec.Vec.deref a.weights) = .ok pending ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim p.gamma) = .ok claimPowers ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
        AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers ∧
      (∀ k : Fin 12, ∃ (a0 a1 : Accumulator) (b0 b1 : BatchWeights),
        a0.next.val=10+k.val ∧
        verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
          proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryFieldEvidence rest proof p a0 g claimPowers) := by
  exact tx2_after_resume_candidate_twelve_actual_fields ops aops rest proof hash obs
    (verifier.resumeWithOps resumeOps inst checkpoint proof public_bytes
      transport.Variant.S2 hash)
    out bout hcanonical hscan h

#print axioms tx2_after_resume_success_inv
#print axioms tx2_after_resume_candidate_twelve_actual_fields
#print axioms resume_model_candidate_twelve_actual_field_evidence
end AspisR1S4Tx2ResumeTwelveFieldEvidenceV2
