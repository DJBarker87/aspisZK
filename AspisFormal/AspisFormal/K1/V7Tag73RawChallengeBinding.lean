import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Tag-73 raw challenge binding

Tag-73 revision 2 binds the complete fixed-width raw sampler inventory after
gamma and alpha-zero.  The number of consumed blocks is explicit and every
unused block is canonically zero.  The fixed 386-byte payload keeps the source
codec and its injectivity independent of rejection-sampling history.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawChallengeBinding

open AspisK1.V7Tag73TranscriptSchedule

inductive BoundChallengeId where
  | gamma
  | alphaZero
  deriving DecidableEq, Repr

def BoundChallengeId.code : BoundChallengeId → UInt8
  | .gamma => 0
  | .alphaZero => 1

theorem bound_challenge_id_code_injective :
    Function.Injective BoundChallengeId.code := by
  intro left right exact
  cases left <;> cases right <;> simp_all [BoundChallengeId.code]

structure RawChallengeBinding where
  id : BoundChallengeId
  /-- Literal count in `1..12`, stored byte-exactly by production Rust. -/
  blocksUsed : UInt8
  blocksUsedPositive : 0 < blocksUsed.toNat
  blocksUsedAtMostTwelve : blocksUsed.toNat ≤ 12
  /-- Consumed blocks followed by canonical zero padding. -/
  blocks : Fin 12 → Digest256
  zeroPadding : ∀ index, blocksUsed.toNat ≤ index.val →
    blocks index = zeroBytes 32

def RawChallengeBinding.data (binding : RawChallengeBinding) : ByteString :=
  [binding.id.code, binding.blocksUsed] ++ encodeBlocks binding.blocks

def rawChallengeBindInput (state : MachineState)
    (binding : RawChallengeBinding) : ByteString :=
  bytes state.digest ++ [domAbsorb, challengeBindLabel] ++ binding.data

theorem raw_challenge_binding_data_length (binding : RawChallengeBinding) :
    binding.data.length = 386 := by
  simp [RawChallengeBinding.data]

theorem raw_challenge_bind_input_length (state : MachineState)
    (binding : RawChallengeBinding) :
    (rawChallengeBindInput state binding).length = 420 := by
  simp [rawChallengeBindInput, raw_challenge_binding_data_length]

private theorem encode_blocks_injective (width : Nat) :
    ∀ count : Nat,
      Function.Injective
        (encodeBlocks : (Fin count → Bytes width) → ByteString) := by
  intro count
  induction count with
  | zero =>
      intro left right _exact
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      intro left right exact
      have splitExact :
          bytes (left 0) ++
              encodeBlocks (fun (index : Fin count) => left index.succ) =
            bytes (right 0) ++
              encodeBlocks (fun (index : Fin count) => right index.succ) := by
        simpa [encodeBlocks, List.ofFn_succ] using exact
      obtain ⟨headExact, tailExact⟩ := List.append_inj splitExact (by simp)
      have headValueExact : left 0 = right 0 :=
        List.ofFn_injective headExact
      have tailValueExact :
          (fun (index : Fin count) => left index.succ) =
            (fun (index : Fin count) => right index.succ) := ih tailExact
      funext index
      refine Fin.cases headValueExact (fun tailIndex => ?_) index
      exact congrFun tailValueExact tailIndex

theorem raw_challenge_binding_data_injective :
    Function.Injective RawChallengeBinding.data := by
  intro left right exact
  have idCodeExact : left.id.code = right.id.code := by
    have headExact := congrArg List.head? exact
    simpa [RawChallengeBinding.data] using headExact
  have idExact : left.id = right.id :=
    bound_challenge_id_code_injective idCodeExact
  have usedExact : left.blocksUsed = right.blocksUsed := by
    have secondExact := congrArg (fun value => value[1]?) exact
    simpa [RawChallengeBinding.data] using secondExact
  have blocksExact : left.blocks = right.blocks := by
    apply encode_blocks_injective 32 12
    have tailExact := congrArg (List.drop 2) exact
    simpa [RawChallengeBinding.data] using tailExact
  cases left
  cases right
  simp_all

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

#print axioms bound_challenge_id_code_injective
#print axioms raw_challenge_binding_data_length
#print axioms raw_challenge_bind_input_length
#print axioms raw_challenge_binding_data_injective
#print axioms raw_challenge_bind_input_injective_for_state

end AspisK1.V7Tag73RawChallengeBinding
