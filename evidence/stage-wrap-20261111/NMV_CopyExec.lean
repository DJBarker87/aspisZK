import NMV_SdkExec
set_option autoImplicit false
namespace NMV_CopyExec
open RSL NMV_WindowEval NMV_SdkExec

def run (a : AccountInfo) (ck : Bytes) (s : SdkState) : Obs (Except ProgramError Unit × SdkState) :=
 bind (acquireExec a .exclusive s) fun r =>
 match r with
 | (.error e,s2) => pure (.error e,s2)
 | (.ok t,s2) =>
   if ck.length != (payload a s2).length then ⟨.abort,[]⟩ else
   bind ⟨.ret (),[.write a.cell ck]⟩ fun _ =>
   let c := s2.cells a.cell
   bind (releaseExec a t .exclusive (s2.put a.cell {c with payload:=ck})) fun s4 =>
   pure (.ok (),s4)

theorem law (a : AccountInfo) (ck : Bytes) (s : SdkState) (env : Env) :
 TX1_344.copyStep a ck s env (run a ck s) := by
 unfold TX1_344.copyStep run
 apply bind_mem _ _ _ _ env (acquire_law a .exclusive s env)
 intro r
 rcases r with ⟨res,s2⟩
 cases res with
 | error e => rfl
 | ok t =>
   simp only
   split
   · rfl
   · apply bind_mem _ _ _ _ env rfl
     intro _
     apply bind_mem _ _ _ _ env (release_law _ _ _ _ env)
     intro _; rfl

#print axioms law
end NMV_CopyExec
