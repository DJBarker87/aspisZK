import NIN_ObserverPredicates
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_Observer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
section
variable {A C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
local notation "cfg" => FIp_Install.configuration err base r
local notation "source" => ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a

/-- Canonical input is from the original first submission on ALL exits.
No hash/byte equivalence or collision exclusion is required for this observer. -/
theorem canonical_from_initial (physical : F3T_Runtime.Runtime)
    (exported : ∀ H run, (eval H physical).2 = some run → run.2.1 =
      F3T_Canon.canonInput (F3T_ByteCarrier.input cfg (submitted (eval H a.first).2))) :
    CanonicalInput copy allocator base err r hashv a physical := by
  intro H run observed
  rw [ART_FirstProjection.original cfg hashv copy allocator CPH_Program.verifier a H]
  exact exported H run observed

/-- Neither canonicalization nor partial execution changes stored/public bytes.
This fixes the exact lower-level payload an observer producer must export. -/
theorem stored_public (H : Bytes → State) :
    let input := F3T_Canon.canonInput (F3T_ByteCarrier.input cfg (submitted (eval H source).2.1))
    input.stored = (MultiproofConeCanonical.bytesOf
      ((eval H a.first).2.entry.buffers ((eval H a.first).2.entry.handles 0).1).val).drop 688 ∧
    input.physical.bytes = MultiproofConeCanonical.bytesOf
      ((eval H a.first).2.entry.buffers ((eval H a.first).2.entry.handles 1).1).val := by
  rw [ART_FirstProjection.original cfg hashv copy allocator CPH_Program.verifier a H]
  exact ⟨rfl,rfl⟩
#print axioms canonical_from_initial
#print axioms stored_public
end
end AspisR1.NIN_Observer
