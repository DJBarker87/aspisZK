import AspisV8R19.R594JointChallengeMass
import AspisV8R19.R599CanonicalFieldTuple
import AspisV8R19.R600ResultEvalLength

set_option autoImplicit false
namespace AspisV8R19.R601ExactFieldMass
open MemoizedProgramLaw OracleResampling IndependentMeanFixedTape
open R592FiniteBlockExecution R594JointChallengeMass R599CanonicalFieldTuple
open R580SourceWordStream R572SequentialWordMass R584IndependentBlockSampler
open R445InitialBlockRejectionLaw SourceDuplexStep QM31SamplerProgram
open AspisV8R15.ExactTowerBase
noncomputable section

def fieldEvent (q : QM31Exact) (out : Option (List Nat)) : ℚ :=
  if out.map SamplerFieldDecode.decode = some q then 1 else 0

theorem canonical_field_event (q : QM31Exact) (xs : List (Fin modulus))
    (hlen : xs.length = 4) :
    fieldEvent q (some (xs.map Fin.val)) =
      tupleEvent (tupleFieldEquiv.symm q) (some (xs.map Fin.val)) := by
  have hq : tupleField (tupleFieldEquiv.symm q) = q := tupleFieldEquiv.apply_symm_apply q
  have he := decode_eq_tuple_iff (by simpa using hlen)
    (fun a ha => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact v.isLt) (tupleFieldEquiv.symm q)
  rw [hq] at he
  simp only [fieldEvent, tupleEvent, Option.map_some, Option.some.injEq]
  rw [he]

theorem block_field_mass (q : QM31Exact) :
    outputMean challengeBlockProgram (fun r => fieldEvent q r.1) =
      ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4 := by
  rw [independent_block_result_law (fieldEvent q)]
  have hm := block_tuple_mass (tupleFieldEquiv.symm q)
  rw [independent_block_result_law (tupleEvent (tupleFieldEquiv.symm q))] at hm
  rw [← hm]
  apply mean_congr
  intro blocks
  generalize hr : resultEval (blockAnswer (extendBlocks blocks)) (limbs 8 4 0) = r
  rcases r with ⟨out,next⟩
  cases out with
  | none => simp [fieldEvent, tupleEvent]
  | some xs =>
      have hlen := R600ResultEvalLength.resultEval_limbs_length
        (blockAnswer (extendBlocks blocks)) 8 4 0 hr
      simpa only [Option.map_some] using canonical_field_event q xs hlen

theorem source_independent_field_mass (s : SourceDuplexStep.State) (q : QM31Exact) :
    outputMean (challengeProgram s) (fun r => fieldEvent q r.1) =
      ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4 := by
  rw [challenge_independent_block]
  exact block_field_mass q

#print axioms canonical_field_event
#print axioms block_field_mass
#print axioms source_independent_field_mass
end
end AspisV8R19.R601ExactFieldMass
