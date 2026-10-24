import S2W_LeadInterface
import S2W_OracleAudit

/-! Continuation 3: an accepted digest call supplies its own returning witness.
No global backend termination is required by the revised caller record.
Historical S2LeadInterface is preserved by the new-module-only rule. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_SuccessOracle
open Aeneas Aeneas.Std Result
open S2Z.Oracle MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Successful-call value transport, including the byte representation. -/
theorem returned_raw {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State)
    (law : CheckpointBytes5Inputs.Oracle D hash H) (parts : Parts) (digest : Digest)
    (returned : D.digest hash parts = ok digest) :
    digest = MultiproofConePhysicalTransport.rawOracle H parts := by
  have value := law parts digest returned
  change AspisV8R19.SqueezeOracleBridge.decodeState digest =
    H (AspisV8R19.SqueezeOracleBridge.flatten parts) at value
  change digest = AspisV8R19.SqueezeOracleBridge.encodeState
    (H (AspisV8R19.SqueezeOracleBridge.flatten parts))
  rw [← value]
  exact (AspisV8R19.SqueezeOracleBridge.array_roundtrip digest).symm

/-- The native source dictionary remains the actual extracted op43. Its
binding to hashv and runtime interpretation are separate named premises. -/
theorem native_success_field (ops : AdapterRw.Ops) (backend : Parts → Result Digest)
    (sha256 H : Bytes → State) (binding : NativeBinding ops backend)
    (runtime : RuntimeSyscall backend sha256) (p1 : P1Realization sha256 H) :
    CheckpointBytes5Inputs.Oracle (leadDigest ops) () H :=
  successful_call ops backend sha256 H binding runtime p1

/-- Historical caller facts imply revised caller facts with every byte,
site, observer, clock and account parameter unchanged. The converse is not
claimed: backend totality was the removed obligation. -/
theorem before_to_after {Observer Hash : Type} (c : S2LeadInterface.Inputs Observer)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2LeadInterface.S2CallerFacts c D hash H stored pub saved parsed) :
    CheckpointBytes5Inputs.Oracle D hash H :=
  S2LeadInterface.checkpoint_oracle D hash H facts.oracle

/-- Nonreturn on an unused input is consistent with the revised law. This
retains the old countermodel instead of silently dropping it after the ruling. -/
theorem masked_success (ops : AdapterRw.Ops) (backend : Parts → Result Digest)
    (sha256 H : Bytes → State) (runtime : RuntimeSyscall backend sha256)
    (p1 : P1Realization sha256 H) (blocked : Parts) :
    let changed := {ops with op43 := fun _ parts => S2W.OracleAudit.mask backend blocked parts}
    CheckpointBytes5Inputs.Oracle (leadDigest changed) () H ∧
    ¬ ∃ digest, (leadDigest changed).digest () blocked = ok digest := by
  dsimp only
  refine ⟨native_success_field _ _ _ _ (fun _ _ => rfl)
    (S2W.OracleAudit.mask_runtime backend sha256 runtime blocked) p1, ?_⟩
  rintro ⟨digest,returned⟩
  change S2W.OracleAudit.mask backend blocked blocked = ok digest at returned
  simp only [S2W.OracleAudit.mask,if_pos rfl] at returned
  cases returned

#print axioms returned_raw
#print axioms native_success_field
#print axioms before_to_after
#print axioms masked_success
#print S2W_LeadInterface.checkpoint_binding
#print S2W_LeadInterface.compose
#print S2W_LeadInterface.multiproof_join
#print S2W_LeadInterface.y1_join
end AspisR1.S2W_SuccessOracle
end
