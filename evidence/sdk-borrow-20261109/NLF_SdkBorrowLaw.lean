import NLF_BorrowBounds
import NLF_SharedDataLaw
import NLF_ExclusiveDataLaw
import NLF_SharedLamportsLaw
import NLF_ExclusiveLamportsLaw
import NLF_DataLenLaw
import NLF_LamportsLaw
import NLF_MetadataLaws
import NLF_ProgramFold
import NLF_CopyStep
import NLF_ThreeAccounts
import NLF_SevenAccounts
import NLF_InitialBinding
import NLF_TX1_Snapshot0
import NLF_TX1_Snapshot1
import NLF_TX1_Snapshot2
import NLF_TX2_Snapshot0
import NLF_TX2_Snapshot1
import NLF_TX2_Snapshot2
import NLF_TX2_Snapshot3
import NLF_TX2_Snapshot4
import NLF_TX2_Snapshot5
import NLF_TX2_Snapshot6
set_option autoImplicit false
namespace NLF_SdkBorrowLaw
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation
/-- Reusable std-interpretation support law for entry and Pool parent folds.
This is NOT a frozen parent/native packet or a soundness theorem. Every native
use must instantiate the pinned wrappers and the SAME runtime-admitted cells.
The Pool uses its already-approved entry-admission item, with this SAME type. -/
theorem admitted_events {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (n : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) n)
    (commands : List NLF_ProgramFold.Command) :
    Invariant (NLF_ProgramFold.run (install h records money) commands) ∧
    (∀ i, flag ((install h records money).state.cells i)=h.counter i) ∧
    (∀ a, a<n → h.ownerLive a=true) := by
  exact ⟨NLF_ProgramFold.fold_invariant _ _ (install_invariant h records money),
    NLF_InitialBinding.all_counter_binding h records money n runtime,runtime.liveAccount⟩

/-- A live token identifies only one cell in EVERY parent state reached by the
fold; this excludes NJN-F2's duplicated exclusive ownership. -/
theorem unique_live_cell (p : Parent) (commands : List NLF_ProgramFold.Command)
    (valid : Invariant p) (i j t : Nat)
    (hi : HasToken ((NLF_ProgramFold.run p commands).state.cells i) t)
    (hj : HasToken ((NLF_ProgramFold.run p commands).state.cells j) t) : i=j :=
  (NLF_ProgramFold.fold_invariant p commands valid).2.2 i j t hi hj

/-- The complete operational trace stays within the deployed signed 64-bit
borrow flag range. This is derived, not a stronger caller precondition. -/
theorem admitted_counter_range {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (n : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) n)
    (commands : List NLF_ProgramFold.Command) :
    NLF_BorrowBounds.Bounded (NLF_ProgramFold.run (install h records money) commands).state ∧
    (∀ i,flag ((install h records money).state.cells i)=h.counter i) :=
  ⟨NLF_BorrowBounds.admitted_bound h records money commands,
    NLF_InitialBinding.all_counter_binding h records money n runtime⟩
#print axioms admitted_counter_range

#print axioms admitted_events
#print axioms unique_live_cell
end NLF_SdkBorrowLaw
