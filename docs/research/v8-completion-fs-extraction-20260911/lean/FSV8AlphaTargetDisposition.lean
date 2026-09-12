import FSV8AlphaChallengeInputBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8AlphaTargetDisposition
open AspisK1.V7FsAokExperiment AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open FSV8AlphaChallengeInputBridge

inductive TargetDisposition (state : OracleState) (input : ShaInput) where
  | priorAdversaryQ1
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 state)
      (inputEq : record.input = input)
  | priorTarget (entry : TableEntry)
      (lookup : lookupEntry state input = some entry)
  | absent
      (lookup : lookupEntry state input = none)

noncomputable def target_disposition (state : OracleState) (input : ShaInput) :
    TargetDisposition state input := by
  classical
  by_cases q1 : ∃ record, record ∈ freezeAdversaryQ1 state ∧ record.input = input
  · let record := Classical.choose q1
    have spec := Classical.choose_spec q1
    exact .priorAdversaryQ1 record spec.1 spec.2
  · by_cases table : lookupEntry state input = none
    · exact .absent table
    · let entry := Classical.choose (Option.ne_none_iff_exists'.mp table)
      let lookup := Classical.choose_spec (Option.ne_none_iff_exists'.mp table)
      exact .priorTarget entry lookup

noncomputable def alpha_target_disposition
    (state : OracleState) (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    TargetDisposition state (alphaCandidateInput afterAlphaNonce) :=
  target_disposition state (alphaCandidateInput afterAlphaNonce)

#print axioms target_disposition
#print axioms alpha_target_disposition
end AspisV8Completion.FSV8AlphaTargetDisposition
