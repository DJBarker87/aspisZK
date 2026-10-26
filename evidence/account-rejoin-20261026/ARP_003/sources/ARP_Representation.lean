import ARP_Interface
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARP_Representation
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment
variable {A F C Tx : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- Recording preserves the ENTIRE outcome and ordered issued log for each H.
Thus every cost/outcome functional on this pair has its original law, without
conditioning, rejection filtering, or deleting adversary queries. -/
theorem original_law (a : Adversary A) (H : Bytes → State) :
    eval H (OracleProgramRecording.record (account c hashv copy allocator id a)) =
      let v := eval H (account c hashv copy allocator id a)
      (v.1,(v.1,v.2)) :=
  OracleProgramRecording.eval_record H _

/-- The exact restricted image on which the proposed quantifier change is
lossless. BankSupported remains an UNPROVED all-world implementation target;
this definition does not turn it into an approved premise or attacker promise. -/
def Covered (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (system : S2W_ExtractionBoundary.Program)
    (P : F3T_ByteCarrier.ByteProver) (r : F3T_Runtime.Runtime) : Prop :=
  ∃ a : Adversary A,
    ARP_Interface.BankSupported c hashv copy allocator id (Tx := Tx) a n1 n2 system ∧
    P = submission a ∧ r = runtime c hashv copy allocator id a

theorem coverage_iff (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (system : S2W_ExtractionBoundary.Program)
    (R : F3T_ByteCarrier.ByteProver → F3T_Runtime.Runtime → Prop) :
    (∀ a : Adversary A,
      ARP_Interface.BankSupported c hashv copy allocator id (Tx := Tx) a n1 n2 system →
      R (submission a) (runtime c hashv copy allocator id a)) ↔
    (∀ P r, Covered c hashv copy allocator id (Tx := Tx) n1 n2 system P r → R P r) := by
  constructor
  · intro all P r ⟨a,supported,hP,hr⟩
    subst P; subst r
    exact all a supported
  · intro all a supported
    exact all _ _ ⟨a,supported,rfl,rfl⟩

/-- The observer construction is not surjective onto the independent runtime
carrier in Rc9. This is a carrier fact, not an attack or a claimed gap for
genuine deployed executions. Genuine deployment coverage still needs proof. -/
theorem not_independent_runtime (a : Adversary A) :
    runtime c hashv copy allocator id a ≠ .done none := by
  intro same
  have equal := congrArg (fun code => (eval (fun _ => SelectedTranscriptParams.params.iv) code).2) same
  rw [runtime_eval] at equal
  cases equal

#print axioms original_law
#print axioms coverage_iff
#print axioms not_independent_runtime
end AspisR1.ARP_Representation
end
