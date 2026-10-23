import AdapterRwModel
import S2LeadInterface

/-! Per-call transport for the adopted owned extraction. The native op43
binding and runtime SHA256 interpretation remain explicit obligations.
P1 is used only as the realization of the ideal oracle in the ROM experiment;
no deterministic SHA256 random-oracle theorem or per-trace equality is claimed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Z.Oracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Parts := Slice (Slice U8)
abbrev Digest := Array U8 32#usize

/-- Nominal dictionary transport, preserving the actual extracted op43. -/
def leadDigest (ops : AdapterRw.Ops) :
    AspisR1Stage2.aspis_core.digest.Digest32 AdapterRw.SolanaDigest :=
  { coremarkerCopyInst := (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops).coremarkerCopyInst
    digest := (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops).digest }

/-- Native wrapper/ABI interpretation, not installed by parameterization. -/
def NativeBinding (ops : AdapterRw.Ops) (hashv : Parts → Result Digest) : Prop :=
  ∀ self parts, ops.op43 self parts = hashv parts

/-- Returning hashv/sol_sha256 semantics on the exact flattened byte input.
This does not assert that every input returns; VM aborts remain outside it. -/
def RuntimeSyscall (hashv : Parts → Result Digest) (sha256 : Bytes → State) : Prop :=
  ∀ parts digest, hashv parts = ok digest →
    AspisV8R19.SqueezeOracleBridge.decodeState digest =
      sha256 (AspisV8R19.SqueezeOracleBridge.flatten parts)

/-- Fixed-oracle realization of P1 in the existing ideal experiment. This is
an experiment premise, never a theorem that SHA256 is a random function. -/
def P1Realization (sha256 H : Bytes → State) : Prop := ∀ bytes, sha256 bytes = H bytes

/-- Each successful digest of the actual owned dictionary has the ideal value.
Quantification is over calls; no trace or successful verifier is a premise. -/
theorem successful_call (ops : AdapterRw.Ops) (hashv : Parts → Result Digest)
    (sha256 H : Bytes → State) (binding : NativeBinding ops hashv)
    (runtime : RuntimeSyscall hashv sha256) (p1 : P1Realization sha256 H) :
    CheckpointBytes5Inputs.Oracle (leadDigest ops) () H := by
  intro parts digest returned
  change ops.op43 () parts = ok digest at returned
  rw [binding] at returned
  exact (runtime parts digest returned).trans (p1 _)

/-- Exact stronger lead field, conditional on total native syscall return.
Totality is named separately; success-conditioned ROM interpretation alone
cannot discharge it. No conclusion is hidden in a new trusted structure. -/
theorem total_call (ops : AdapterRw.Ops) (hashv : Parts → Result Digest)
    (sha256 H : Bytes → State) (binding : NativeBinding ops hashv)
    (runtime : ∀ parts, hashv parts = ok
      (AspisV8R19.SqueezeOracleBridge.encodeState
        (sha256 (AspisV8R19.SqueezeOracleBridge.flatten parts))))
    (p1 : P1Realization sha256 H) :
    ∀ parts, (leadDigest ops).digest () parts =
      ok (MultiproofConePhysicalTransport.rawOracle H parts) := by
  intro parts
  change ops.op43 () parts = _
  rw [binding, runtime, p1]
  rfl

/-- The original extraction dictionary and transported dictionary perform the
same call, including failure/divergence; no ideal interpretation is needed. -/
theorem dictionary_call (ops : AdapterRw.Ops) (self : AdapterRw.SolanaDigest)
    (parts : Parts) :
    (leadDigest ops).digest self parts =
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops).digest self parts := rfl

#print axioms successful_call
#print axioms total_call
#print axioms dictionary_call
end AspisR1.S2Z.Oracle
end
