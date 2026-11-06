import NLF_SevenAccounts
import NLF_ExclusiveBracket
set_option autoImplicit false
namespace NLF_ThreeAccounts
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation NLF_SnapshotFold

def accounts : List Nat := [0,1,2]

theorem tx1_snapshots {F : Type} (h : S2Trust.Heap F) (records : Nat → Account) (money : Nat → Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) 3) :
    let p := install h records money
    let r := run p accounts
    r.1.state=p.state ∧ r.1.next=3 ∧ Invariant r.1 ∧
    r.1.events=schedule p.state 0 accounts ∧ r.2=replies p.state 0 accounts ∧
    (∀ a, a<3 → h.ownerLive a=true) := by
  dsimp only
  refine ⟨run_frame _ _,?_,run_invariant _ _ (install_invariant h records money),?_,run_replies _ _,runtime.liveAccount⟩
  · simpa [install,accounts] using run_next (install h records money) accounts
  · simpa [install] using run_events (install h records money) accounts

/-- The SDK ABI portion of stage1: three snapshots finish (including their
Drops) before the checkpoint exclusive acquisition, one KMX-composed copy,
and Drop. src is the SAME child-produced value, supplied by the caller's child
packet; this is a support theorem, never an admitted parent row root. -/
theorem tx1_exclusive_copy {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (src : List UInt8)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) 3)
    (len : src.length=(h.payload (h.accounts 2).1).descriptor.length) :
    let s := (run (install h records money) accounts).1.state
    let i := (s.accounts 2).data
    try_borrow_mut_data s 2 3 = (put s i {s.cells i with writer:=some 3},.ok ⟨i,3,.exclusive⟩) ∧
    NLF_ExclusiveBracket.copyDrop s 2 3 src =
      .ok (put s i {s.cells i with payload:={(s.cells i).payload with bytes:=src}}) ∧
    h.ownerLive 2=true := by
  dsimp only
  rw [run_frame]
  refine ⟨?_,?_,runtime.liveAccount 2 (by decide)⟩
  · apply NLF_ExclusiveBracket.exclusive_admission <;> rfl
  · apply NLF_ExclusiveBracket.copy_drop
    · rfl
    · simpa [install,NLF_Admission.initial,bytes_length] using len

/-- Distinct keys are used only to frame proof/public cells against checkpoint
writes. Identity and zero counters come from runtime admission, not address
comparison or a returned-success premise. -/
theorem tx1_proof_public_frame {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (v : Payload)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) 3)
    (distinct0 : (records 0).key≠(records 2).key)
    (distinct1 : (records 1).key≠(records 2).key) :
    let s := (install h records money).state
    (put s (s.accounts 2).data {s.cells (s.accounts 2).data with payload:=v}).cells (s.accounts 0).data = s.cells (s.accounts 0).data ∧
    (put s (s.accounts 2).data {s.cells (s.accounts 2).data with payload:=v}).cells (s.accounts 1).data = s.cells (s.accounts 1).data := by
  dsimp only
  constructor
  · apply put_other
    exact NLF_Admission.different_keys h _ 3 0 2 runtime (by decide) (by decide) distinct0
  · apply put_other
    exact NLF_Admission.different_keys h _ 3 1 2 runtime (by decide) (by decide) distinct1

#print axioms tx1_snapshots
#print axioms tx1_exclusive_copy
#print axioms tx1_proof_public_frame
end NLF_ThreeAccounts
