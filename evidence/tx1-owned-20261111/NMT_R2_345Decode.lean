import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepDecode (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (allocationIf (C.decodeReachesAlloc s.publicData) (allocation 3)) fun _ =>
 match C.decodeStatement s.publicData with
 | none => silent (.error .invalidAccountData)
 | some st => tryObs (NMT_R2_Observation.allocation (allocation 4)) fun _ => next ⟨s,st⟩

theorem stepDecode_valid (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (suffix : C.Statement → RS Bytes) (env : Env)
 (later : ∀ st, suffix st env (next ⟨s,st⟩)) :
 RS.seq (RS.lift (Spec.allocIf (C.decodeReachesAlloc s.publicData)))
  (RS.bind (RS.ofOption (C.decodeStatement s.publicData) .invalidAccountData)
   (fun st => RS.seq (RS.lift Spec.alloc) (suffix st))) env (stepDecode V C allocation s next) := by
 apply try_valid _ _ _ _ env (allocationIf_valid _ _ env)
 intro _
 cases hd : C.decodeStatement s.publicData with
 | none =>
  simp only [hd,RS.ofOption,RS.bind_throw]
  rfl
 | some st =>
  simp only [hd,RS.ofOption,RS.bind_pure]
  apply try_valid _ _ _ _ env (allocation_valid _ env)
  intro _
  exact later st
#print axioms stepDecode_valid
end NMT_R2_345
