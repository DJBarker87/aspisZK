import NDO_JFn_HashBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Resume
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- Source resume at the exact retained buffers, with the true oracle
realization boundary visible. No numeric SHA256 realization is asserted. -/
theorem source {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  obtain ⟨hp,hu,hc⟩ := (JFn_HashBoundary.calls_iff H D hash).mpr realizes
  exact (JFo_ResumeNative.source (JFn_HashBoundary.dictionary H D) hash hp hu hc).2

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  have eq : (⟨saved.val,saved.property⟩ : Slice U8)=JFx_NativeBytes.checkpoint := Subtype.ext same
  rw [eq]
  exact source H D hash realizes

/-- A uniform numeric realization claim would be false. This refutes only
that over-quantified statement, not a concrete SHA256 fixture or deployed law. -/
theorem no_universal_realization : ¬∀ H : Bytes → State, JFn_HashBoundary.Realizes H := by
  intro all
  let zero : Bytes → State := fun _ _ => ⟨0,by omega⟩
  have hp := (all zero).1
  have first := congrArg (fun s : State => (s ⟨0,by omega⟩).val) hp
  change 0=85 at first
  omega

#print axioms source
#print axioms on_saved
#print axioms no_universal_realization
end AspisR1.JFn_Resume
end
