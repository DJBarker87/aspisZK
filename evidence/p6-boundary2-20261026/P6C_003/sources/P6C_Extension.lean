import P6C_Accepted
import Op5T_P6
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Extension
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open MultiproofConePhysicalTransport MultiproofConeRef

/-- Mathematical total extension only. The fallback defines unused values;
it does not assert that the runtime returns on those inputs. -/
def total (hashv : Parts → Result Digest) (H : Bytes → State) (parts : Parts) : Digest :=
  match hashv parts with
  | .ok digest => digest
  | _ => rawOracle H parts

theorem agrees (hashv : Parts → Result Digest) (H : Bytes → State)
    (parts : Parts) (digest : Digest) (returned : hashv parts = ok digest) :
    total hashv H parts = digest := by simp only [total,returned]

theorem realization (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (parts : Parts) :
    total hashv H parts = rawOracle H parts := by
  cases returned : hashv parts with
  | fail e => simp only [total,returned]
  | div => simp only [total,returned]
  | ok digest =>
    have decoded := (syscall.returningValue parts digest returned).trans (p1.realization _)
    simp only [total,returned]
    change digest = encodeState (H (flatten parts))
    rw [← decoded]
    exact (array_roundtrip digest).symm

def dictionary (hashv : Parts → Result Digest) (H : Bytes → State) :
    aspis_core.digest.Digest32 Unit :=
  {coremarkerCopyInst := {cloneInst := {clone := fun x => ok x}},
    digest := fun _ parts => ok (total hashv H parts)}

/-- The five mathematical gates are now derived, for the total extension.
Actual source preservation is a separate theorem below; this dictionary is
never claimed to be the actual partial runtime dictionary on rejected runs. -/
theorem boundary (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    MultiproofConeP6Frozen2Stage.P6Boundary (dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf :=
  Op5T_P6.boundary _ () H (fun parts => congrArg Result.ok (realization hashv sha256 H p1 syscall parts))

/-- No all-input return assumption: both Result and every issued attempt are
unchanged on an accepted source execution. -/
theorem source_preserved (hashv : Parts → Result Digest) (H : Bytes → State)
    {A : Type} (code : Code A) (before : Log) (value : A)
    (accepted : (run hashv code before).1 = ok value) :
    run (fun parts => ok (total hashv H parts)) code before = run hashv code before :=
  P6C_Accepted.extension_irrelevant hashv _
    (fun parts digest returned => congrArg Result.ok (agrees hashv H parts digest returned))
    code before value accepted

#print axioms agrees
#print axioms realization
#print axioms boundary
#print axioms source_preserved
end AspisR1.P6C_Extension
end
