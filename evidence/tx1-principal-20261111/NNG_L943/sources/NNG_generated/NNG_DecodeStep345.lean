import NNG_Steps345
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepDecode (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (allocationIf (C.decodeReachesAlloc s.publicData) (allocation 3)) fun _ =>
 match hd : C.decodeStatement s.publicData with
 | none=>silent (.error .invalidAccountData)
 | some st=>tryObs (NNG_Pure345.allocation (allocation 4)) fun _=>next ⟨s,st,hd⟩

theorem stepDecode_valid (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (suffix : C.Statement → RS Bytes) (env : Env)
 (later : ∀ st (decoded : C.decodeStatement s.publicData=some st), suffix st env (next ⟨s,st,decoded⟩)) :
 RS.seq (RS.lift (Spec.allocIf (C.decodeReachesAlloc s.publicData)))
  (RS.bind (RS.ofOption (C.decodeStatement s.publicData) .invalidAccountData)
   (fun st=>RS.seq (RS.lift Spec.alloc) (suffix st))) env (stepDecode V C allocation s next) := by
 apply try_valid _ _ _ _ env (allocationIf_valid _ _ env)
 intro _
 cases hd : C.decodeStatement s.publicData with
 | none=>simp only [stepDecode,hd,RS.ofOption,RS.bind_throw];rfl
 | some st=>
  simp only [stepDecode,hd,RS.ofOption,RS.bind_pure]
  apply try_valid _ _ _ _ env (allocation_valid _ env)
  intro _
  exact later st hd
#print axioms stepDecode_valid
end AspisR1.NNG_Phases345
