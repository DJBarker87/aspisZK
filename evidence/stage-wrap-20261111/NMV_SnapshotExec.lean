import NMV_SdkExec
set_option autoImplicit false
namespace NMV_SnapshotExec
open RSL NMV_WindowEval NMV_SdkExec

/-- The snapshot SDK/std window on every account length, byte value, metadata
record and alias/token state. `allocation t` selects the actual allocation arm. -/
def run (allocation : Nat → Bool) (a : AccountInfo) (x y : Nat) (s : SdkState) : Obs (OwnedAccount × SdkState) :=
 bind (acquireExec a .shared s) fun r =>
 match r with
 | (.error e,s1) => pure (⟨a.key,a.owner,a.is_signer,a.is_writable,a.executable,.error e,.error e⟩,s1)
 | (.ok t,s1) =>
   let data := payload a s1
   let n := data.length
   let admitted := n==x || n==y
   bind (if admitted then allocExec (allocation t) else pure ()) fun _ =>
   bind (releaseExec a t .shared s1) fun s2 =>
   pure (⟨a.key,a.owner,a.is_signer,a.is_writable,a.executable,.ok n,
          if admitted then .ok data else .error .invalidAccountData⟩,s2)

theorem law (allocation : Nat → Bool) (a : AccountInfo) (x y : Nat) (s : SdkState) (env : Env) :
 RSL.snapshot a x y s env (run allocation a x y s) := by
 unfold RSL.snapshot run
 apply bind_mem _ _ _ _ env (acquire_law a .shared s env)
 intro r
 rcases r with ⟨res,s1⟩
 cases res with
 | error e => rfl
 | ok t =>
   apply bind_mem
   · split
     · exact alloc_law _ env
     · rfl
   · intro _
     apply bind_mem _ _ _ _ env (release_law a t .shared s1 env)
     intro _; rfl

#print axioms law
end NMV_SnapshotExec
