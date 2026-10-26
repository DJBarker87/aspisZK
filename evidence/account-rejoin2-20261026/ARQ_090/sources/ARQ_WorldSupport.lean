import ARQ_Transport
import SCF_RequiredTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_WorldSupport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment S2W_D189Consolidation

/-- UNPROVED per-world implementation support, NOT a trust item. Every field
is a retained native/runtime/game observation on the actual response-selected
entries. There is no model acceptance, recovery, collision or desired bound. -/
structure NativeAt {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A) (H : Bytes → State) where
  sha256 : Bytes → State
  p1 : S2W_ExtractionBoundary.P1 sha256 H
  syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256
  saved : alloc.vec.Vec U8
  post1 : Heap (Nat → Record)
  post2 : Heap (Nat → Record)
  final1 : A
  final2 : A
  w1 : W
  w2 : W
  admission1 : RuntimeEntrypointAdmission L (eval H a.first).2.entry w1 3
  admission2 : RuntimeEntrypointAdmission L
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry w2 7
  accepted1 : first native1 copy allocator (eval H a.first).2.entry CPH_Program.verifier
    (eval H a.first).2.data (eval H a.first).2.state = ok (.Ok (saved,post1,final1))
  accepted2 : let j := (eval H (a.second (eval H a.first).2 saved post1 final1)).2
    second native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state = ok (.Ok (post2,final2))
  p : CPG_Projection.Observations Tx A
  t : Tx
  u : Tx
  actions : List (CPP_BankState.Action A)
  game : CPH_Game.DeployedPairExecution p t u (eval H a.first).2.entry
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry saved actions native1 native2 copy allocator CPH_Program.verifier
  RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
    (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8))
    (CPG_Projection.before p) (CPG_Projection.tentative p) (CPG_Projection.success p) (CPG_Projection.loaded p)

/-- No filtering, altered cost law, or promise imposed on the adversary.
Proving this support for the ORIGINAL deployed distribution is still required.
Packaging the retained fields is NOT premise-removal credit. -/
def Supported {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A) : Prop :=
  ∀ H : Bytes → State,
    accepted (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true →
    Nonempty (NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)

#print NativeAt
#print Supported
end AspisR1.ARQ_WorldSupport
end
