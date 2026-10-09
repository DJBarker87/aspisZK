import FSV7OODBodyScript
import FSNonzeroQM31
import FSExposureOrder

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace AspisV8Completion.FSV8PostOODGammaScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
open FSV7OODSampler FSV8OODBodyScript FSV7OODBodyScript
open FSNonzeroQM31 FSExposureOrder FSFirstFresh

abbrev Bytes := List UInt8
abbrev HashBlock := FSBoundedTranscript.Block
abbrev Point := FSV7OODBodyScript.Point
abbrev OODResult := FSV7OODBodyScript.Result
abbrev Gamma := FSNonzeroQM31.K

noncomputable section
local instance : DecidableEq Point := Classical.decEq _

def batchNonceBytes (body : Bytes) : Bytes := (body.drop 11204).take 8

def sourceThenGammaScript {n m : Nat}
    (firstWork : Point → Script Bytes HashBlock Unit n)
    (secondWork : Point → Point → Script Bytes HashBlock Unit m)
    (body : Bytes) (digest : HashBlock) :
    Script Bytes HashBlock
      (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error) (OODResult × Gamma) × HashBlock)
      ((1 + 3*66) + (((1+m)+594+1+n)+198)) :=
  bind (m := 199) (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
      fun (source : Except FSOODSampler.Error OODResult × HashBlock) =>
    match source.1 with
    | .error e => .done (Except.error (Sum.inl e), source.2)
    | .ok out =>
      bind (m := 198) (absorbScript source.2 28 (batchNonceBytes body)) fun afterNonce =>
        bind (m := 0) (FSNonzeroQM31.nonzeroScript 3 afterNonce)
          fun (gamma : Except FSNonzeroQM31.Error Gamma × HashBlock) =>
            (.done (match gamma.1 with
              | .error e => (Except.error (Sum.inr e), gamma.2)
              | .ok value => (Except.ok (out, value), gamma.2)) :
              Script Bytes HashBlock
                (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
                  (OODResult × Gamma) × HashBlock) 0)

theorem successful_sourceThenGamma_components {n m : Nat}
    (firstWork : Point → Script Bytes HashBlock Unit n)
    (secondWork : Point → Point → Script Bytes HashBlock Unit m)
    (body : Bytes) (digest : HashBlock) (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle)
    (out : OODResult) (gamma : Gamma) (finalDigest : HashBlock)
    (success : (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 =
      some (.ok (out, gamma), finalDigest)) :
    ∃ sourceDigest,
      (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest) oracle).1 =
        some (.ok out, sourceDigest) ∧
      let afterNonce := absorb tape
        (⟨sourceDigest,
          (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
            oracle).2⟩ : FSBoundedTranscript.Transcript)
        28 (batchNonceBytes body)
      (run tape (FSNonzeroQM31.nonzeroScript 3 afterNonce.digest)
        afterNonce.oracle).1 = some (.ok gamma, finalDigest) := by
  unfold sourceThenGammaScript at success
  rw [run_bind] at success
  cases hs : (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest) oracle).1 with
  | none => simp [hs] at success
  | some source =>
    rcases source with ⟨sourceResult, sourceDigest⟩
    cases sourceResult with
    | error e => simp [hs, run] at success
    | ok sourceOut =>
      simp only [hs] at success
      rw [run_bind] at success
      have absorbExact := run_absorb tape
        (⟨sourceDigest, (run tape
          (FSV7OODBodyScript.sourceScript firstWork secondWork body digest) oracle).2⟩ :
          FSBoundedTranscript.Transcript)
        28 (batchNonceBytes body)
      rw [absorbExact] at success
      simp only [Prod.fst, Prod.snd] at success
      rw [run_bind] at success
      cases hg : (run tape (FSNonzeroQM31.nonzeroScript 3
          (absorb tape
            (⟨sourceDigest, (run tape
                (FSV7OODBodyScript.sourceScript firstWork secondWork body digest) oracle).2⟩ :
              FSBoundedTranscript.Transcript)
            28 (batchNonceBytes body)).digest)
          (absorb tape
            (⟨sourceDigest, (run tape
                (FSV7OODBodyScript.sourceScript firstWork secondWork body digest) oracle).2⟩ :
              FSBoundedTranscript.Transcript)
            28 (batchNonceBytes body)).oracle).1 with
      | none => simp [hg] at success
      | some gammaPair =>
        rcases gammaPair with ⟨gammaResult, gammaDigest⟩
        cases gammaResult with
        | error e => simp [hg, run] at success
        | ok gammaValue =>
          simp [hg, run] at success
          rcases success with ⟨⟨rfl, rfl⟩, rfl⟩
          exact ⟨sourceDigest, rfl, hg⟩

theorem successful_sourceThenGamma_nonzero {n m : Nat}
    (firstWork : Point → Script Bytes HashBlock Unit n)
    (secondWork : Point → Point → Script Bytes HashBlock Unit m)
    (body : Bytes) (digest : HashBlock) (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle)
    (out : OODResult) (gamma : Gamma) (finalDigest : HashBlock)
    (success : (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 =
      some (.ok (out, gamma), finalDigest)) : gamma ≠ 0 := by
  obtain ⟨sourceDigest, _, hg⟩ :=
    successful_sourceThenGamma_components firstWork secondWork body digest tape oracle
      out gamma finalDigest success
  let afterNonce := absorb tape
    (⟨sourceDigest,
      (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
        oracle).2⟩ : FSBoundedTranscript.Transcript)
    28 (batchNonceBytes body)
  exact FSNonzeroQM31.nonzero_success_ne tape 3
    afterNonce gamma
    (by
      have exactRun := FSNonzeroQM31.run_nonzero tape 3 afterNonce
      have runFirst := congrArg Prod.fst exactRun
      have hgrun : (run tape (FSNonzeroQM31.nonzeroScript 3 afterNonce.digest)
          afterNonce.oracle).1 = some (.ok gamma, finalDigest) := by
        simpa only [afterNonce] using hg
      exact (congrArg Prod.fst (Option.some.inj (hgrun.symm.trans runFirst))).symm)

theorem chronological_membership
    (log : FSExposureOrder.Log) (secondInput nonceInput gammaInput : Bytes)
    (hsecond : secondInput ∈ inputs log) (hnonce : nonceInput ∈ inputs log)
    (hgamma : gammaInput ∈ inputs log)
    (order : firstExposure log secondInput < firstExposure log nonceInput ∧
      firstExposure log nonceInput < firstExposure log gammaInput) :
    firstExposure log secondInput < firstExposure log nonceInput ∧
      firstExposure log nonceInput < firstExposure log gammaInput ∧
      secondInput ∈ inputs log ∧ nonceInput ∈ inputs log ∧ gammaInput ∈ inputs log :=
  ⟨order.1, order.2, hsecond, hnonce, hgamma⟩

#print axioms successful_sourceThenGamma_components
#print axioms successful_sourceThenGamma_nonzero
end
end AspisV8Completion.FSV8PostOODGammaScript
