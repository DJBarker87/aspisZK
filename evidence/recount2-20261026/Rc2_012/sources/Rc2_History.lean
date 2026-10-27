import CPS_SourceTop
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc2_History
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_NativeConsolidation MultiproofConeCanonical S2W_CommittedCheckpoint S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- CPS correlated history, guarded by every unadopted association and runtime
law. The cuts are the enclosing accepted pair, never a second selected pair. -/
def Facts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) : Prop :=
  ∀ (keyLaw : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (initial : CPP_BankState.Bank) (layout1 : Layout)
    (entry1 : e1 = load initial.cells (CPP_BankState.layout initial layout1))
    (actions : List (CPP_BankState.Action A))
    (positive : 0 < initial.lamports (layout1.handles 2).1)
    (Tx Key : Type) (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → CPR_DataPersistence.Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Bytes)
    (law : CPR_DataPersistence.TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (physicalKey : Key) (adjacent : next t u) (eligible : ordinary t physicalKey)
    (tentativeView : tentative t physicalKey = CPR_DataPersistence.snapshot
      (CPP_BankHistory.run n1 n2 copy allocator id
        (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions).1 (layout1.handles 2).1)
    (status : success t = true)
    (entry2View : loaded u physicalKey = some (bytesOf (e2.buffers (e2.handles 6).1).val)),
    ∃ version : S2X.CheckpointVersionBinding
      (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val),
      version.events = (eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id
        (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions)).2.2 ∧
      bytesOf s.checkpoint.val = payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768

theorem derive {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (e1 e2 : Entry) (data1 : Slice U8) (state1 final1 : A)
    (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s) :
    Facts c hashv n1 n2 copy allocator id e1 e2 saved post1 H f s := by
  intro keyLaw initial layout1 entry1 actions positive Tx Key next ordinary before tentative success loaded law t u physicalKey adjacent eligible tentativeView status entry2View
  let version := CPR_DataWriter.on_cuts c keyLaw n1 n2 hashv extraction copy std allocator id
    initial (CPP_BankState.layout initial layout1) e1 e2 entry1 data1 state1 final1 saved post1 accepted1
    actions positive next ordinary before tentative success loaded law t u physicalKey adjacent eligible
    tentativeView status entry2View f s cuts
  refine ⟨version,?_,S2X.checkpoint_persistence _ _ version⟩
  exact (CPS_BankRecorder.events c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall
    (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions).symm

#print axioms derive
end AspisR1.Rc2_History
end
