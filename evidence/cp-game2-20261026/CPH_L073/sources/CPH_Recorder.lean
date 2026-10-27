import CPH_Trace
import CPS_BankRecorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_Recorder
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem physical {Tx A F C : Type} (p : Observations Tx A) (t u : Tx)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (actions : List (Action A))
    (c : DrvC_Installation.Configuration F C)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    (eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 saved) (p.actions t))).2 =
        (p.parentTentative t,p.physicalEvents t) ∧
    (eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id
      (cached (p.bank u)) (p.actions u))).2 = (p.parentTentative u,p.physicalEvents u) := by
  obtain ⟨writer,reader⟩ := CPH_Trace.derive game
  exact ⟨(CPS_BankRecorder.result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall _ _).trans writer,
    (CPS_BankRecorder.result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall _ _).trans reader⟩

#print axioms physical
end AspisR1.CPH_Recorder
end
