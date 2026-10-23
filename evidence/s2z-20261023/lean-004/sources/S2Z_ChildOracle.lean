import S2Z_Oracle
import S2B_LeadCarriers

/-! Compose the per-call owned dictionary law with existing child execution
results. Child reification/native installation remains open and explicit.
No native call clock is assigned a numerical rank. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Z.ChildOracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1Stage2 CheckpointBytes5Effect
open S2Z.Oracle

/-- A returning reified child preserves its entire ordered query history,
including when `value` is an inner Err. No suffix is erased on rejection. -/
theorem consistent_child {A : Type} (ops : AdapterRw.Ops)
    (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (binding : NativeBinding ops hashv) (runtime : RuntimeSyscall hashv sha256)
    (p1 : P1Realization sha256 H) (child : Code A) (before after : Log) (value : A)
    (initial : AspisR1DigestLogCarrier.Consistent H (S2B_LeadCarriers.observe before))
    (returned : run (leadDigest ops) () child before = ok (value,after)) :
    AspisR1DigestLogCarrier.Consistent H (S2B_LeadCarriers.observe after) := by
  exact S2B_LeadCarriers.ordered_calls () (leadDigest ops) () H (fun _ : Unit => child)
    before after value (successful_call ops hashv sha256 H binding runtime p1) initial returned

/-- The existing extracted checkpoint resume contributes exactly proof,
public, checksum, in that order, using the OWNED caller's dictionary. This
instantiates its per-call oracle without assuming equality of whole traces.
The native verifier-to-resume effect port is not discharged by this theorem. -/
theorem checkpoint_resume (ops : AdapterRw.Ops)
    (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (binding : NativeBinding ops hashv) (runtime : RuntimeSyscall hashv sha256)
    (p1 : P1Realization sha256 H) (resumeOps : ResumeOps)
    (ne_sound : ∀ (s : Slice U8) (a : Array U8 32#usize),
      resumeOps.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (ck proof publicInput : Slice U8) (variant : transport.Variant)
    (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (before : Log)
    (length : ck.val.length = 1768)
    (returned : verifier.resumeWithOps resumeOps (leadDigest ops) ck proof publicInput variant () =
      ok (.Ok (prepared,accumulator))) :
    ∃ c : Tx2ResumeDigests.Calls (leadDigest ops) () ck proof publicInput,
      run (leadDigest ops) () (CheckpointBytes5Resume.program resumeOps ck proof publicInput variant)
        before = ok (.Ok (prepared,accumulator), before ++
          [(c.proofParts,c.proofDigest),(c.publicParts,c.publicDigest),(c.checksumParts,c.checksumDigest)]) ∧
      CheckpointBytes5Inputs.observe
        [(c.proofParts,c.proofDigest),(c.publicParts,c.publicDigest),(c.checksumParts,c.checksumDigest)] =
        [(MultiproofConeCanonical.bytesOf proof.val,H (MultiproofConeCanonical.bytesOf proof.val)),
         (MultiproofConeCanonical.bytesOf publicInput.val,H (MultiproofConeCanonical.bytesOf publicInput.val)),
         (OraclePortPhysicalFrameDraft.domain ++ (MultiproofConeCanonical.bytesOf ck.val).take 1736,
          H (OraclePortPhysicalFrameDraft.domain ++ (MultiproofConeCanonical.bytesOf ck.val).take 1736))] := by
  obtain ⟨c,execution⟩ := CheckpointBytes5Trace.successful_log resumeOps (leadDigest ops)
    ne_sound ck proof publicInput variant () prepared accumulator before returned
  exact ⟨c,execution,CheckpointBytes5Inputs.calls_observation (leadDigest ops) () H
    (successful_call ops hashv sha256 H binding runtime p1) ck proof publicInput c length⟩

#print axioms consistent_child
#print axioms checkpoint_resume
end AspisR1.S2Z.ChildOracle
end
