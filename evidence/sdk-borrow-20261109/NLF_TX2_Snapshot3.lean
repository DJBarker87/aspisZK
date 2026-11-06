import NLF_SnapshotOccurrence
set_option autoImplicit false
namespace NLF_TX2_Snapshot3
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation NLF_SnapshotFold
/-- Frozen r1_pool_adapter_owned.rs:474. Snapshot's token ABI only;
owned Vec allocation/copy and later child calls remain with the parent owner. -/
theorem at_site {F : Type} (h : S2Trust.Heap F) (records : Nat → Account) (money : Nat → Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) 7) :
    let p := (run (install h records money) ([0,1,2] : List Nat)).1
    let r := NLF_SnapshotEvents.step p 3
    let g : Guard := ⟨(h.accounts 3).1,([0,1,2] : List Nat).length,.shared⟩
    r.1.state=(install h records money).state ∧ r.1.next=([0,1,2] : List Nat).length+1 ∧
    r.2=.ok ((install h records money).state.cells g.cell).payload ∧
    r.1.events=schedule (install h records money).state 0 ([0,1,2] : List Nat) ++
      [.acquire 3 ([0,1,2] : List Nat).length .shared (.ok g),
       .deref g (.ok ((install h records money).state.cells g.cell).payload),.release g (.ok ())] ∧
    h.ownerLive 3=true ∧ h.counter (h.accounts 3).1=0 := by
  have base := NLF_SnapshotOccurrence.packet h records money ([0,1,2] : List Nat) 3
  dsimp only at base ⊢
  exact ⟨base.1,base.2.1,base.2.2.1,base.2.2.2,
    runtime.liveAccount 3 (by decide),runtime.counterZero 3 (by decide)⟩
#print axioms at_site
end NLF_TX2_Snapshot3
