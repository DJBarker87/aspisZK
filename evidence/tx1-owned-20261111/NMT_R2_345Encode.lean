import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepEncode (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : Validated V C)
 (next : Candidate V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 match C.encodeCandidate s.statement with
 | none => silent (.error .invalidAccountData)
 | some bytes => next ⟨s,bytes⟩

theorem stepEncode_valid (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : Validated V C)
 (next : Candidate V C → Obs (Except ProgramError Bytes)) (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (RS.ofOption (C.encodeCandidate s.statement) .invalidAccountData) suffix env
  (stepEncode V C s next) := by
 unfold stepEncode
 cases he : C.encodeCandidate s.statement with
 | none => simp only [RS.ofOption,RS.bind_throw]; rfl
 | some bytes => simp only [RS.ofOption,RS.bind_pure]; exact later bytes
#print axioms stepEncode_valid
end NMT_R2_345
