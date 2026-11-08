import NNG_Steps345
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def afterDecode (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (r : Option C.Statement) : C.decodeStatement s.publicData=r → Obs (Except ProgramError Bytes) :=
 match r with
 | none=>fun _=>silent (.error .invalidAccountData)
 | some st=>fun hd=>tryObs (NNG_Pure345.allocation (allocation 4)) fun _=>next ⟨s,st,hd⟩

def stepDecode (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (allocationIf (C.decodeReachesAlloc s.publicData) (allocation 3)) fun _ =>
 afterDecode V C allocation s next (C.decodeStatement s.publicData) rfl

theorem afterDecode_valid (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (suffix : C.Statement → RS Bytes) (env : Env) (r : Option C.Statement)
 (hd : C.decodeStatement s.publicData=r)
 (later : ∀ st (decoded : C.decodeStatement s.publicData=some st), suffix st env (next ⟨s,st,decoded⟩)) :
 RS.bind (RS.ofOption r .invalidAccountData)
  (fun st=>RS.seq (RS.lift Spec.alloc) (suffix st)) env (afterDecode V C allocation s next r hd) := by
 cases r with
 | none=>rw [RS.ofOption,RS.bind_throw];rfl
 | some st=>
  rw [RS.ofOption,RS.bind_pure]
  apply try_valid _ _ _ _ env (allocation_valid _ env)
  intro _
  exact later st hd
#print axioms afterDecode_valid

theorem stepDecode_valid (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (suffix : C.Statement → RS Bytes) (env : Env)
 (later : ∀ st (decoded : C.decodeStatement s.publicData=some st), suffix st env (next ⟨s,st,decoded⟩)) :
 RS.seq (RS.lift (Spec.allocIf (C.decodeReachesAlloc s.publicData)))
  (RS.bind (RS.ofOption (C.decodeStatement s.publicData) .invalidAccountData)
   (fun st=>RS.seq (RS.lift Spec.alloc) (suffix st))) env (stepDecode V C allocation s next) := by
 apply try_valid _ _ _ _ env (allocationIf_valid _ _ env)
 intro _
 exact afterDecode_valid V C allocation s next suffix env _ rfl later
#print axioms stepDecode_valid
end AspisR1.NNG_Phases345
