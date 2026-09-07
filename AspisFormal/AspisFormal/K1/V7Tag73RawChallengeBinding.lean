import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Tag-73 raw challenge binding

Tag-73 revision 2 binds the canonical decoded value after gamma and
alpha-zero. This makes each later transcript state causally depend on the
challenge while keeping the binding payload fixed at 17 bytes. The prior
digest already binds the exact sampler-block chain.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawChallengeBinding

open AspisK1.V7Tag73TranscriptSchedule

theorem bound_challenge_id_code_injective :
    Function.Injective BoundChallengeId.code := by
  intro left right exact
  cases left <;> cases right <;> simp_all [BoundChallengeId.code]

structure RawChallengeBinding where
  id : BoundChallengeId
  value : Qm31Bytes

def RawChallengeBinding.data (binding : RawChallengeBinding) : ByteString :=
  [binding.id.code] ++ bytes binding.value

def rawChallengeBindInput (state : MachineState)
    (binding : RawChallengeBinding) : ByteString :=
  bytes state.digest ++ [domAbsorb, challengeBindLabel] ++ binding.data

theorem raw_challenge_binding_data_length (binding : RawChallengeBinding) :
    binding.data.length = 17 := by
  simp [RawChallengeBinding.data]

theorem raw_challenge_bind_input_length (state : MachineState)
    (binding : RawChallengeBinding) :
    (rawChallengeBindInput state binding).length = 51 := by
  simp [rawChallengeBindInput, raw_challenge_binding_data_length]

theorem raw_challenge_binding_data_injective :
    Function.Injective RawChallengeBinding.data := by
  intro left right exact
  have idCodeExact : left.id.code = right.id.code := by
    have headExact := congrArg List.head? exact
    simpa [RawChallengeBinding.data] using headExact
  have idExact : left.id = right.id :=
    bound_challenge_id_code_injective idCodeExact
  have valueExact : left.value = right.value := by
    have tailExact := congrArg (List.drop 1) exact
    have bytesExact : bytes left.value = bytes right.value := by
      simpa [RawChallengeBinding.data] using tailExact
    exact List.ofFn_injective bytesExact
  cases left
  cases right
  simp_all

def actualBinding (id : BoundChallengeId) (value : Qm31Bytes) :
    RawChallengeBinding where
  id := id
  value := value

theorem actual_binding_data_exact (id : BoundChallengeId)
    (value : Qm31Bytes) :
    (Payload.challengeBind id value).data =
      (actualBinding id value).data := by
  rfl

theorem raw_challenge_bind_input_injective_for_state (state : MachineState) :
    Function.Injective (rawChallengeBindInput state) := by
  intro left right exact
  apply raw_challenge_binding_data_injective
  have tailExact := congrArg (List.drop 34) exact
  have leftDrop : List.drop 34 (rawChallengeBindInput state left) =
      left.data := by
    dsimp [rawChallengeBindInput]
    convert List.drop_append_length
      (l₁ := bytes state.digest ++ [domAbsorb, challengeBindLabel])
      (l₂ := left.data) using 1 <;> simp
  have rightDrop : List.drop 34 (rawChallengeBindInput state right) =
      right.data := by
    dsimp [rawChallengeBindInput]
    convert List.drop_append_length
      (l₁ := bytes state.digest ++ [domAbsorb, challengeBindLabel])
      (l₂ := right.data) using 1 <;> simp
  exact leftDrop.symm.trans (tailExact.trans rightDrop)

/-- Equality of two literal binding inputs fixes the typed binding even when
their predecessor transcript states are not known equal in advance. -/
theorem raw_challenge_bind_input_eq_implies_binding_eq
    (leftState rightState : MachineState)
    (left right : RawChallengeBinding)
    (exact : rawChallengeBindInput leftState left =
      rawChallengeBindInput rightState right) :
    left = right := by
  apply raw_challenge_binding_data_injective
  have tailExact := congrArg (List.drop 34) exact
  have leftDrop : List.drop 34 (rawChallengeBindInput leftState left) =
      left.data := by
    dsimp [rawChallengeBindInput]
    convert List.drop_append_length
      (l₁ := bytes leftState.digest ++ [domAbsorb, challengeBindLabel])
      (l₂ := left.data) using 1 <;> simp
  have rightDrop : List.drop 34 (rawChallengeBindInput rightState right) =
      right.data := by
    dsimp [rawChallengeBindInput]
    convert List.drop_append_length
      (l₁ := bytes rightState.digest ++ [domAbsorb, challengeBindLabel])
      (l₂ := right.data) using 1 <;> simp
  exact leftDrop.symm.trans (tailExact.trans rightDrop)

#print axioms bound_challenge_id_code_injective
#print axioms raw_challenge_binding_data_length
#print axioms raw_challenge_bind_input_length
#print axioms raw_challenge_binding_data_injective
#print axioms raw_challenge_bind_input_injective_for_state
#print axioms raw_challenge_bind_input_eq_implies_binding_eq

end AspisK1.V7Tag73RawChallengeBinding
