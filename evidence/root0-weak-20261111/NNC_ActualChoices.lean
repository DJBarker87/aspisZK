import NNC_RecSelect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_ActualChoices
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment

/-- The entries are defined from this adversary's actual adaptive choices. -/
def first {A : Type} (a : Adversary A) (H : Bytes → State) : FirstInputs A :=
  (eval H a.first).2

def second {A : Type} (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A) : SecondInputs A :=
  (eval H (a.second (first a H) saved post final)).2

/-- Realizes is an equality by construction at EVERY oracle, not an event
on which a probability may be conditioned. The adversary is never replaced. -/
theorem realizes {A : Type} (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A) :
    (eval H a.first).2 =
      ⟨(first a H).entry, (first a H).data, (first a H).state⟩ ∧
    (eval H (a.second (first a H) saved post final)).2 =
      ⟨(second a H saved post final).entry, (second a H saved post final).data,
        (second a H saved post final).slot, (second a H saved post final).state⟩ :=
  ⟨rfl, rfl⟩

/-- The entire execution observer retains rejected first phases and their
queries. A reached second phase receives the SAME successful first reply.
No Root0, TX2 model evaluation, or Realizes test enters this program. -/
def program {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (a : Adversary A) :
    Program Bytes State (FirstInputs A × Option (alloc.vec.Vec U8 × Heap (Nat → Record) × A × SecondInputs A)) :=
  bind a.first fun i =>
    match S2W_D189Wrappers.first native1 copy allocator i.entry CPH_Program.verifier i.data i.state with
    | .ok (.Ok (saved, post, final)) =>
      bind (a.second i saved post final) fun j => .done (i, some (saved,post,final,j))
    | _ => .done (i,none)

theorem issued {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (a : Adversary A) (H : Bytes → State) :
    (eval H (program native1 copy allocator a)).1 =
      ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H := by
  unfold program ARW_Induced.issued
  simp only [eval_bind]
  split <;> simp_all only [eval_bind,eval,List.append_nil]

theorem selected {A C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (a : Adversary A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator
      (first a H).entry CPH_Program.verifier (first a H).data (first a H).state =
        ok (.Ok (saved,post,final)))
    (Q : Nat) (queries : ∀ K,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a K).length ≤ Q) :
    ARQ_Observer.select (FIp_Install.configuration err base reservation) CPH_Program.verifier
      (eval H (ARX_LocalCharge.bounded
        (ART_PartialAccount.account (FIp_Install.configuration err base reservation)
          hashv copy allocator CPH_Program.verifier a) Q)).2 =
    P2P_NativeSelection.pair (DrvC_Installation.sdk (FIp_Install.configuration err base reservation))
      CPH_Program.verifier (first a H).entry (second a H saved post final).entry
        (second a H saved post final).data (second a H saved post final).slot := by
  exact NNC_RecSelect.selects copy allocator base err reservation native1 native2 hashv
    extraction sha256 H p1 syscall (first a H).entry (second a H saved post final).entry
    (first a H).data (second a H saved post final).data (second a H saved post final).slot
    (first a H).state (second a H saved post final).state final saved post accepted1 a Q queries rfl rfl

#print axioms realizes
#print axioms issued
#print axioms selected
end AspisR1.NNC_ActualChoices
