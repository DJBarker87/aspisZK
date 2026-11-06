import NLF_SdkBorrowLaw
set_option autoImplicit false
namespace NLK_ParentFold
open NLF_ParentModel
/-- The shared parent state keeps the current SDK token ledger. Extra fields
are the caller's own program counter, owned carriers and chronological cuts. -/
structure State (Local : Type) where
  sdk : Parent
  caller : Local

def borrowStep {Local : Type} (s : State Local) (c : NLF_ProgramFold.Command) : State Local :=
  {s with sdk := NLF_ProgramFold.step s.sdk c}

def borrowFold {Local : Type} (s : State Local) (cs : List NLF_ProgramFold.Command) : State Local :=
  {s with sdk := NLF_ProgramFold.run s.sdk cs}

theorem source_order {Local : Type} (s : State Local)
    (xs ys : List NLF_ProgramFold.Command) :
    borrowFold s (xs ++ ys) = borrowFold (borrowFold s xs) ys := by
  simp only [borrowFold, NLF_ProgramFold.source_order]

theorem step_invariant {Local : Type} (s : State Local)
    (c : NLF_ProgramFold.Command) (valid : Invariant s.sdk) :
    Invariant (borrowStep s c).sdk :=
  NLF_ProgramFold.step_invariant s.sdk c valid

/-- Runtime admission binds the SAME account records and cells. This is local
support, not a parent invocation certificate and not a proposed row root. -/
theorem admitted_fold {F Local : Type} (heap : AspisR1.S2Trust.Heap F)
    (records : Nat → NLF_SdkModel.Account) (money : Nat → Nat) (n : Nat)
    (runtime : AspisR1.AdapterRw.RuntimeEntrypointAdmission heap (fun a => (records a).key) n)
    (caller : Local) (cs : List NLF_ProgramFold.Command) :
    Invariant (borrowFold ⟨NLF_RuntimeInterpretation.install heap records money,caller⟩ cs).sdk ∧
    (∀ i, NLF_RefCell.flag ((NLF_RuntimeInterpretation.install heap records money).state.cells i) = heap.counter i) ∧
    (∀ a, a<n → heap.ownerLive a=true) :=
  NLF_SdkBorrowLaw.admitted_events heap records money n runtime cs

#print source_order
#print axioms source_order
#print step_invariant
#print axioms step_invariant
#print admitted_fold
#print axioms admitted_fold
end NLK_ParentFold
