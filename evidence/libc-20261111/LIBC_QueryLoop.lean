import LIBC_Bytes
import LIBC_Usize
import LIBC_ResultGraph
import LIBC_VStateCarriers
import LIBC_QueryOps
import NFS_QueryLoopRoot
set_option autoImplicit false
noncomputable section
namespace LIBC_QueryLoop
open Aeneas Aeneas.Std Result AspisR1 RSL
abbrev Args := Bytes × LIB_VCarriers.Prepared × LIB_VCarriers.Acc × LIB_VCarriers.E29 × LIB_VCarriers.Geo × LIB_VCarriers.Weights × Nat
abbrev Output := Except LIB_VCarriers.VErr (LIB_VCarriers.Acc × LIB_VCarriers.Weights)
def nativeP (a : Args) := NFW_PreparedPort.prepared a.2.1
def nativeA (a : Args) := LIBC_VStateCarriers.toAcc a.2.2.1
def nativeG (a : Args) := NFW_PreparedPort.map NFW_PreparedPort.e a.2.2.2.1
def geo (a : Args) := a.2.2.2.2.1
def pending (a : Args) := a.2.2.2.2.2.1
def finish (a : Args) := a.2.2.2.2.2.2
def Domain (a : Args) : Prop :=
 finish a=10 ∧ (nativeA a).next.val=0 ∧
 NFS_PacketRoot.Domain (LIBC_Bytes.raw a.1) (nativeP a) (nativeG a) (geo a) 0 10#usize (nativeA a) (pending a)
def model (a : Args) (_ : Env) := Port3_QueryInstall.result
 (NFG_QueryLoopDefs.run
  (NFS_QueryLoopRoot.child (NFS_CallerDomains.select LIBC_QueryOps.seed)
   (LIBC_Bytes.raw a.1) (nativeP a) (nativeG a) (geo a) 0 0)
  10#usize 10 (.Ok (nativeA a,pending a)))
def port : core.result.Result (AspisR1Stage2.verifier.Accumulator × LIB_VCarriers.Weights) VTop_Stages.verifier.Error → Output
 | .Ok (a,b) => .ok (LIBC_VStateCarriers.fromAcc a,b) | .Err e => .error e
def child : Child Args Output := ⟨Domain,fun a => LIB_Carriers.resultGraph port (model a) (fun _ => [])⟩
def value (a : Args) (env : Env) : Output := LIBC_ResultGraph.value port (.error .Query) (model a env)
theorem returns (a : Args) (env : Env) : NND_Returned.Returns (child.law a) env (value a env) :=
 LIBC_ResultGraph.returns _ _ _ _ env
/-- One arbitrary native step and the existing Lean induction; all callee
operations are now fixed. No whole-buffer native run or child success premise. -/
theorem source (a : Args) (env : Env) (domain : Domain a) :
 model a env = Port3_QueryInstall.result
  (Port3_NativeQueryBody.verifier.candidate.query_loop LIBC_QueryOps.ops
   (LIBC_Bytes.raw a.1) (nativeP a) (nativeA a) (nativeG a) none (geo a) (pending a)
   (LIBC_Usize.raw (finish a))) := by
 rw [domain.1]
 have ten : LIBC_Usize.raw 10 = 10#usize := LIBC_Usize.from_native 10#usize
 rw [ten]
 unfold model
 rw [NFS_QueryLoopRoot.tx1 _ _ _ _ _ _ _ 0 0 domain.2.2.gCanonical domain.2.2.invariant domain.2.1]
 rfl
theorem graph (a : Args) (env : Env) (o : Obs Output) :
 child.law a env o ↔ o = LIB_Carriers.resultObs port [] (model a env) := Iff.rfl
#print axioms returns
#print axioms source
#print axioms graph
end LIBC_QueryLoop
