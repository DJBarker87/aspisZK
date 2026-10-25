import AuS1_Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Row30
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

theorem reached (e : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (input scratch : Array aspis_core.field.WideExact 29#usize) (out : verifier.Prepared)
    (variant : view.variant = .S2)
    (success : erase (PreparedSourceEffects.prepare e D sem view hash input) = ok (.Ok out,scratch)) :
    ∃ (before after : transcript.Transcript H) (root : Array U8 32#usize)
      (bytes1 bytes2 : alloc.vec.Vec U8) (alpha : aspis_core.field.WideExact),
      core.option.Option.unwrap view.folded_root = ok root ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 256#usize)
        (Array.to_slice root) = ok bytes1 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 view.round1 = ok bytes2 ∧
      erase (e.scalar D before 30#u8 bytes2.deref false) = ok (alpha,after) ∧
      ∀ frame, Read (observe (run (e.scalar D before 30#u8 bytes2.deref false)).1) frame →
        Read (observe (run (PreparedSourceEffects.prepare e D sem view hash input)).1) frame := by
  let log := observe (run (PreparedSourceEffects.prepare e D sem view hash input)).1
  have included : ∀ frame, Read (observe (run (PreparedSourceEffects.prepare e D sem view hash input)).1) frame → Read log frame := fun _ h => h
  change ∃ (before after : transcript.Transcript H) (root : Array U8 32#usize)
    (bytes1 bytes2 : alloc.vec.Vec U8) (alpha : aspis_core.field.WideExact), _ ∧ _ ∧ _ ∧ _ ∧
    ∀ frame, Read (observe (run (e.scalar D before 30#u8 bytes2.deref false)).1) frame → Read log frame
  unfold PreparedSourceEffects.prepare at success included
  obtain ⟨state,h_state,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨start,h_start,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨gamma,h_gamma,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨inactive,h_inactive,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨slice,h_slice,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨kappa,h_kappa,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨alpha0,h_alpha0,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨folds,h_folds,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  rw [erase_lift] at h_folds
  change transport.Variant.folds view.variant = ok folds at h_folds
  have folds_eq : folds = 2#usize := by
    rw [variant] at h_folds
    exact (Result.ok.inj h_folds).symm
  subst folds
  simp only [if_pos rfl] at success included
  obtain ⟨capacity,h_capacity,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨root,h_root,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨rootSlice,h_rootSlice,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨bytes1,h_bytes1,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨bytes2,h_bytes2,success,sub⟩ := right_read _ _ _ success
  have included := fun frame member => included frame (sub frame member)
  obtain ⟨a,ha,hk,sub⟩ := AuS1_Trace.success_bind _ _ _ success
  have contains := left_read _ _ _ success
  refine ⟨alpha0.2,a.2,root,bytes1,bytes2,a.1,?_,?_,?_,ha,?_⟩
  · exact h_root
  · exact h_bytes1
  · exact h_bytes2
  · intro frame member
    exact included frame (contains frame member)

#print axioms reached
end AspisR1.AuS1_Row30
end
