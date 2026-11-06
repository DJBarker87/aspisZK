import NLF_SnapshotFold
import NLF_RuntimeInterpretation
set_option autoImplicit false
namespace NLF_SevenAccounts
open NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation NLF_SnapshotFold
open AspisR1

def accounts : List Nat := [0,1,2,3,4,5,6]

/-- Source stage2_owned.rs:470-478 has SEQUENTIAL snapshots, each guard dropped
before the next acquisition; errors are deferred owned values, not early exits.
This token ABI law retains every result and ordered event. It does not assert
Clock, snapshot Vec allocation/copy, or stage2_owned's native result. -/
theorem tx2_acquisition_cleanup {F : Type} (h : S2Trust.Heap F)
    (records : Nat → Account) (money : Nat → Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) 7) :
    let p := install h records money
    let r := run p accounts
    r.1.state = p.state ∧ r.1.next = 7 ∧ Invariant r.1 ∧
    r.1.events = schedule p.state 0 accounts ∧ r.2 = replies p.state 0 accounts ∧
    (∀ a, a<7 → h.ownerLive a=true) := by
  dsimp only
  refine ⟨run_frame _ _,?_,run_invariant _ _ (install_invariant h records money),?_,run_replies _ _,runtime.liveAccount⟩
  · simpa [install,accounts] using run_next (install h records money) accounts
  · simpa [install] using run_events (install h records money) accounts

/-- Cell aliases are exactly duplicate admitted keys, even across two of the
seven source occurrences. No pairwise-distinctness premise is smuggled in. -/
theorem tx2_cell_identity {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) 7)
    (a b : Nat) (ha : a<7) (hb : b<7) :
    (((install h records money).state.accounts a).data = ((install h records money).state.accounts b).data ↔
      (records a).key=(records b).key) := by
  exact NLF_Admission.aliases_exactly h _ 7 a b runtime ha hb

#print axioms tx2_acquisition_cleanup
#print axioms tx2_cell_identity
end NLF_SevenAccounts
