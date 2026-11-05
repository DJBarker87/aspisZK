import NHZ_Realization
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_Observer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

section
variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
local notation "cfg" => FIp_Install.configuration err base r
local notation "source" => ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a

/-- Item 1: full charged chronological trace, with repetitions. -/
def OuterTrace (physical : F3T_Runtime.Runtime) : Prop :=
  ∀ H, (eval H physical).1 = (eval H source).1
/-- Item 2: exact admitted support, including the outside-game none branch. -/
def AdmittedSupport (physical : F3T_Runtime.Runtime) : Prop :=
  ∀ H, ((eval H physical).2).isSome = true ↔
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator base err r n1 n2 hashv a H)
/-- Item 3: the nested log is the SAME full occurrence log, not a set. -/
def NestedEvents (physical : F3T_Runtime.Runtime) : Prop :=
  ∀ H run, (eval H physical).2 = some run → run.1 = (eval H source).1
/-- Item 4 includes semantic input, proof, stored bytes AND physical public bytes. -/
def CanonicalInput (physical : F3T_Runtime.Runtime) : Prop :=
  ∀ H run, (eval H physical).2 = some run → run.2.1 =
    F3T_Canon.canonInput (F3T_ByteCarrier.input cfg (submitted (eval H source).2.1))
/-- Item 5 is literally BOTH source Results; no honest-run or accept-only domain. -/
def LiteralFlag (physical : F3T_Runtime.Runtime) : Prop :=
  ∀ H run, (eval H physical).2 = some run → run.2.2 = accepted (eval H source).2
end
end AspisR1.NIN_Observer
