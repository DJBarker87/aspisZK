/-
DGP_HostDigest: the host instantiation that resolves NNH_ preflight P2.

STATEMENT FILE FOR NNH_: NOT COMPILED HERE.  Its imports (Aeneas, the
NNH_/LIB_/S2W_ closure) exist only on the build host.  The same proofs are
compiled over abstract carriers in DGP_DigestMirror.lean (core Lean, exit 0;
see DGP_MIRROR_STDOUT.txt).  NNH_ compiles this file in one focused scope
(MemoryHigh 6G, MemoryMax 8G, swap 0, Lean -M7000) before S2.

Target not yet established.  No sorry, no axiom declaration, no new premise.
The two averaging obligations are stated as `def ... : Prop`, not assumed.
-/
import NNH_CorrectConfiguration
import NNH_HostEnv
import NNH_RecordedCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.DGP_HostDigest
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-! ## 1. Instantiation (three host definitions) -/

/-- Concatenation of the RSL partition, in the protocol byte carrier. -/
def hostFlatten (ps : List RSL.Bytes) : Bytes :=
  (ps.flatMap NNC_ByteCarriers.nativeList).map decodeByte

/-- `NNH_HostEnv.Runtime.sha c := shaReply c.sha256`: the env sha256 reply is
the headline sha256 of the concatenation (hashv semantics). -/
def shaReply (sha256 : Bytes → State) : List RSL.Bytes → RSL.B32 :=
  fun ps => NNC_ResumeEvents.digest (encodeState (sha256 (hostFlatten ps)))

/-- The headline binder `hashv` is instantiated (it leaves the retained Ctx,
like native1/native2 and the allocator) at the existing total adapter. -/
abbrev hashvInst (sha256 : Bytes → State) : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest :=
  hashAdapter sha256

/-- Host env at the instantiation (pda/clock/reservation unchanged). -/
abbrev envInst (sha256 : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
    (clock : Except RSL.ProgramError UInt64) (reservation : NP6_StdModel.Reservation) : RSL.Env :=
  NNH_HostEnv.environment (shaReply sha256) pda clock reservation

/-! ## 2. Discharge lemmas -/

/-- The headline `syscall` binder at the instantiation. -/
theorem syscall (sha256 : Bytes → State) :
    S2W_ExtractionBoundary.RuntimeSyscall (hashvInst sha256) sha256 :=
  ⟨fun parts digest returned => by
    cases returned
    exact state_roundtrip _⟩

theorem key_digest (out : Array U8 32#usize) :
    LIB_Env.nativeKey (NNC_ResumeEvents.digest out) = out := by
  apply Subtype.ext
  change NNC_ByteCarriers.nativeList (NNC_ByteCarriers.host out.val) = out.val
  exact NNC_ByteCarriers.native_host out.val

theorem flatten_parts (parts : S2Z.Oracle.Parts) :
    hostFlatten (NNC_ResumeEvents.parts parts) = flatten parts := by
  simp only [hostFlatten, NNC_ResumeEvents.parts, flatten, List.flatMap_map,
    NNC_ByteCarriers.native_host]

/-- The literal op43 reply equals the instantiated hashv, pointwise. -/
theorem op43_value (sha256 : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
    (clock : Except RSL.ProgramError UInt64) (reservation : NP6_StdModel.Reservation)
    (parts : S2Z.Oracle.Parts) :
    LIB_Env.hashv (envInst sha256 pda clock reservation) parts = hashvInst sha256 parts := by
  change Result.ok (LIB_Env.nativeKey (NNC_ResumeEvents.digest
    (encodeState (sha256 (hostFlatten (NNC_ResumeEvents.parts parts)))))) =
    Result.ok (encodeState (sha256 (flatten parts)))
  rw [key_digest, flatten_parts]

/-- A0 `digestSource` at the literal configuration, missing := missingLit. -/
theorem digestSource (m0 : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
    (sha256 : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
    (clock : Except RSL.ProgramError UInt64) (reservation : NP6_StdModel.Reservation)
    (err : NFN_NEW_GeometryDictionary.CE) :
    ∀ self parts,
      (NNH_CorrectConfiguration.sdk m0 (envInst sha256 pda clock reservation) err reservation).op43
        self parts = S2W_DigestExtraction.digest (hashvInst sha256) self parts := by
  intro self parts
  rw [S2W_DigestExtraction.digest_eq_hashv]
  change LIB_Env.hashv (envInst sha256 pda clock reservation) parts = _
  exact op43_value sha256 pda clock reservation parts

/-- Per-world P1 at sha256 := H. -/
theorem p1 (H : Bytes → State) : S2W_ExtractionBoundary.P1 H H := ⟨fun _ => rfl⟩

#print axioms syscall
#print axioms key_digest
#print axioms flatten_parts
#print axioms op43_value
#print axioms digestSource
#print axioms p1

/-! ## 3. Averaging obligations (S7), stated, not assumed

With sha256 := H, both hashvInst and the op43 slot of missingLit vary with H.
NNH_RecordedCharge.bound is proved for a FIXED base and hashv.  The bound
transfers only through the two equalities below.  O1 is the host form of
DGP_DigestMirror.program_adapter_fixed (ART_PartialProgram reads hashv's
status only).  O2 says the account syntax and observer never read op43
values.  If O2 is false, report it; do not add a premise. -/

def O1 : Prop :=
  ∀ {C : Type} (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (base : DrvC_Installation.Configuration FIo_Install.W C) (err : C)
    (r : NP6_StdModel.Reservation) (sha256 : Bytes → State) (d0 : S2Z.Oracle.Digest)
    (a : SCE_Experiment.Adversary Bool) (Q : Nat),
    NNH_RecordedCharge.recorder copy base err r (hashvInst sha256) a Q =
      NNH_RecordedCharge.recorder copy base err r (fun _ => .ok d0) a Q

def O2 : Prop :=
  ∀ (m0 : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (env env' : RSL.Env) (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (a : SCE_Experiment.Adversary Bool) (Q : Nat),
    env.pda = env'.pda → env.clock = env'.clock → env.reservation = env'.reservation →
    NNH_RecordedCharge.recorder copy
        (IDa_Deployed.deployedConfiguration
          (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env) env) err r)
        err r hashv a Q =
      NNH_RecordedCharge.recorder copy
        (IDa_Deployed.deployedConfiguration
          (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env') env') err r)
        err r hashv a Q

end AspisR1.DGP_HostDigest
end
