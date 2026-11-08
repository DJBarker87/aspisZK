import NMV_WindowRoots
set_option autoImplicit false
namespace NMV_SdkExec
open RSL NMV_WindowEval

def acquireExec (a : AccountInfo) (k : Kind) (s : SdkState) : Obs (Except ProgramError Nat × SdkState) :=
 let c := s.cells a.cell
 let t := s.next
 let yes := match k with | .shared => sharedOk c | .exclusive => exclusiveOk c
 if yes then
   let c' := match k with
     | .shared => { c with readers := t::c.readers }
     | .exclusive => { c with writer := some t }
   ⟨.ret (.ok t,{(s.put a.cell c') with next:=t+1}),[.acquire a.cell t k true]⟩
 else ⟨.ret (.error .accountBorrowFailed,{s with next:=t+1}),[.acquire a.cell t k false]⟩

def releaseExec (a : AccountInfo) (t : Nat) (k : Kind) (s : SdkState) : Obs SdkState :=
 let c := s.cells a.cell
 let c' := match k with
   | .shared => {c with readers:=c.readers.erase t}
   | .exclusive => {c with writer:=none}
 ⟨.ret (s.put a.cell c'),[.release a.cell t k]⟩

theorem acquire_law (a : AccountInfo) (k : Kind) (s : SdkState) (env : Env) :
 acquire a k s env (acquireExec a k s) := by
 unfold acquire acquireExec
 cases k <;> (simp only; split)
 all_goals
   refine Or.inl ⟨(),_,_,rfl,rfl,?_⟩
   rfl

theorem release_law (a : AccountInfo) (t : Nat) (k : Kind) (s : SdkState) (env : Env) :
 release a t k s env (releaseExec a t k s) := by
 unfold release releaseExec
 exact Or.inl ⟨(),_,_,rfl,rfl,rfl⟩

/-- Allocation's actual success/abort choice; no allocation-success premise. -/
def allocExec (yes : Bool) : Obs Unit := if yes then pure () else ⟨.abort,[]⟩

theorem alloc_law (yes : Bool) (env : Env) : Spec.alloc env (allocExec yes) := by
 cases yes
 · exact Or.inr rfl
 · exact Or.inl rfl

#print axioms acquire_law
#print axioms release_law
#print axioms alloc_law
end NMV_SdkExec
