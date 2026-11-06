import NLK_SdkBytes
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneBorrow
open Aeneas Aeneas.Std Result NLF_ParentModel NLF_SdkModel
/-- This is the returned VALUE layer only. Allocation effects belong inside
the actual callback and are NOT discharged by this total value function. -/
def child (b : Payload) : core.result.Result NLA_LaneAssemble.Lane NKF_BoxModel.PE :=
 if h : b.bytes.length=768 then
  NLK_LaneProgram.referenceValue (NLK_SdkBytes.payload b (NLK_SdkBytes.lane_bound b h))
 else .Err .InvalidAccountData

def run (p : Parent) (account : Nat) :=
 NLK_ProgramBorrowScope.run p account (fun b => ok (child b))

theorem source (p : Parent) (account : Nat) :
 run p account =
 let r := NLF_SnapshotEvents.step p account
 ⟨r.1,ok (match r.2 with | .ok b => child b | .error _ => .Err .AccountBorrowFailed)⟩ :=
 NLK_ReturningBorrow.complete p account child

theorem state_frame (p : Parent) (account : Nat) :
 (run p account).parent.state=p.state := by
 rw [source];exact NLF_SnapshotEvents.step_frame p account

theorem token_events (p : Parent) (account : Nat) :
 (run p account).parent.events=p.events++NLF_SnapshotEvents.events p.state account p.next := by
 rw [source];rfl

theorem admitted {F : Type} (heap : AspisR1.S2Trust.Heap F)
 (records : Nat → Account) (money : Nat → Nat) (n account : Nat)
 (runtime : AspisR1.AdapterRw.RuntimeEntrypointAdmission heap (fun a => (records a).key) n) :
 Invariant (run (NLF_RuntimeInterpretation.install heap records money) account).parent ∧
 (∀ i,NLF_RefCell.flag ((NLF_RuntimeInterpretation.install heap records money).state.cells i)=heap.counter i) ∧
 (∀ a,a<n → heap.ownerLive a=true) := by
 refine ⟨NLK_ProgramBorrowScope.invariant _ _ _ (NLF_RuntimeInterpretation.install_invariant _ _ _),?_,runtime.liveAccount⟩
 exact NLF_InitialBinding.all_counter_binding heap records money n runtime

#print source
#print axioms source
#print state_frame
#print axioms state_frame
#print token_events
#print axioms token_events
#print admitted
#print axioms admitted
end NLK_LaneBorrow
