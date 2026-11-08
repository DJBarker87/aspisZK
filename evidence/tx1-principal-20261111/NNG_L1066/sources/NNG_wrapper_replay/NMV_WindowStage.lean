import NMV_WindowClock
set_option autoImplicit false
namespace NMV_WindowStage
open RSL NMV_WindowEval NMV_WindowClock

/-- Fission copy with SDK/std/runtime windows interpreted on full carriers.
No child law is baked into the interpreter; replies retain all alternatives. -/
def stage2 (w : Windows)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (a : TX2_240.Args) (s : SdkState) (env : Env) : Obs (Except ProgramError Unit × SdkState) :=
 if TX2_240.badRoute a then pure (.error .invalidInstructionData,s) else
 bind (w.clear [] env) fun _ =>
 bind (snapshots w a.accounts TX2_240.snapLens s env) fun r =>
 bind (w.clock env) fun c =>
 bind (child ⟨a.program_id,r.1,a.data,c⟩ env) fun res => pure (res,r.2)

def stage1 (w : Windows)
 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (a : TX1_344.Args) (s : SdkState) (env : Env) : Obs (Except ProgramError Unit × SdkState) :=
 if TX1_344.badRoute a then pure (.error .invalidInstructionData,s) else
 bind (snapshots w a.accounts TX1_344.snapLens s env) fun r =>
 bind (child ⟨a.program_id,r.1,a.data⟩ env) fun res =>
 match res with
 | .error e => pure (.error e,r.2)
 | .ok ck => match a.accounts[2]? with
   | none => ⟨.abort,[]⟩
   | some a2 => w.copy a2 ck r.2 env

theorem cut240 (w : Windows)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 NMV_RslFold.stage2 child a s env (stage2 w child a s env) := by
 unfold NMV_RslFold.stage2 stage2
 split
 · rfl
 · apply bind_mem _ _ _ _ env (w.clear_law [] env)
   intro _
   apply bind_mem _ _ _ _ env (snapshots_law w _ _ s env)
   intro r
   rw [exact_clock]
   have ht := bind_mem (NMV_RslFold.observed child ⟨a.program_id,r.1,a.data,env.clock⟩)
     (fun res => Spec.pure (res,r.2))
     (child ⟨a.program_id,r.1,a.data,env.clock⟩ env)
     (fun res => pure (res,r.2)) env rfl (fun _ => rfl)
   have he := bind_mem (Spec.emit (.clock env.clock))
     (fun _ => Spec.bind (NMV_RslFold.observed child ⟨a.program_id,r.1,a.data,env.clock⟩)
       (fun res => Spec.pure (res,r.2)))
     ⟨.ret (),[.clock env.clock]⟩
     (fun _ => bind (child ⟨a.program_id,r.1,a.data,env.clock⟩ env) (fun res => pure (res,r.2)))
     env rfl (fun _ => ht)
   refine Or.inl ⟨env.clock, [], _, rfl, he, ?_⟩
   rfl

theorem cut344 (w : Windows)
 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (a : TX1_344.Args) (s : SdkState) (env : Env) :
 NMV_RslFold.stage1 child a s env (stage1 w child a s env) := by
 unfold NMV_RslFold.stage1 stage1
 split
 · rfl
 · apply bind_mem _ _ _ _ env (snapshots_law w _ _ s env)
   intro r
   apply bind_mem _ _ _ _ env rfl
   intro res
   cases res with
   | error e => rfl
   | ok ck =>
     cases ha : a.accounts[2]? with
     | none => exact rfl
     | some a2 => exact w.copy_law a2 ck r.2 env

#print axioms cut240
#print axioms cut344
end NMV_WindowStage
