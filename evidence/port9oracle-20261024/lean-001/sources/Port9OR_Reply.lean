import Port8EFF_CheckpointCode

/-! Exact finite byte/state conversion. No quotient, truncation, hash agreement,
or returning-domain assumption is needed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Reply
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytesDigest

-- UScalar.ofNat takes an in-range proof; this is not modular reduction.
def byte (b : AspisV8R19.DuplexFrames.Byte) : U8 :=
  U8.ofNat b.val (by have := b.isLt; scalar_tac)

def digest (s : State) : CheckpointBytes5Effect.Digest :=
  ⟨List.ofFn (fun j : Fin 32 => byte (s j)), by simp⟩

theorem state_digest (s : State) : stateOf (digest s) = s := by
  funext j
  apply Fin.ext
  simp [stateOf,digest,byte,AspisV8R19.SqueezeOracleBridge.decodeByte]

theorem digest_state (d : CheckpointBytes5Effect.Digest) : digest (stateOf d) = d := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [digest,d.property]
  · intro i hi hj
    simp only [digest,List.getElem_ofFn]
    apply UScalar.eq_of_val_eq
    simp [byte,stateOf,AspisV8R19.SqueezeOracleBridge.decodeByte]

#print axioms state_digest
#print axioms digest_state
end AspisR1.Port9OR_Reply
end
