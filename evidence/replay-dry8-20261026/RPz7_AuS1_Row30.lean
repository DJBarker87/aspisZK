import RPz7_AuS1_Suffix
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
    (s0 : erase (PreparedSourceEffects.prepare e D sem view hash input) = ok (.Ok out,scratch)) :
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
  have inc0 : ∀ frame, Read (observe (run (PreparedSourceEffects.prepare e D sem view hash input)).1) frame → Read log frame := fun _ h => h
  change ∃ (before after : transcript.Transcript H) (root : Array U8 32#usize)
    (bytes1 bytes2 : alloc.vec.Vec U8) (alpha : aspis_core.field.WideExact), _ ∧ _ ∧ _ ∧ _ ∧
    ∀ frame, Read (observe (run (e.scalar D before 30#u8 bytes2.deref false)).1) frame → Read log frame
  unfold PreparedSourceEffects.prepare at s0 inc0
  obtain ⟨state,h_state,s1,sub1⟩ := right_read _ _ _ s0
  have inc1 := fun frame member => inc0 frame (sub1 frame member)
  obtain ⟨start,h_start,s2,sub2⟩ := right_read _ _ _ s1
  have inc2 := fun frame member => inc1 frame (sub2 frame member)
  obtain ⟨gamma,h_gamma,s3,sub3⟩ := right_read _ _ _ s2
  have inc3 := fun frame member => inc2 frame (sub3 frame member)
  obtain ⟨inactive,h_inactive,s4,sub4⟩ := right_read _ _ _ s3
  have inc4 := fun frame member => inc3 frame (sub4 frame member)
  obtain ⟨slice,h_slice,s5,sub5⟩ := right_read _ _ _ s4
  have inc5 := fun frame member => inc4 frame (sub5 frame member)
  obtain ⟨kappa,h_kappa,s6,sub6⟩ := right_read _ _ _ s5
  have inc6 := fun frame member => inc5 frame (sub6 frame member)
  obtain ⟨alpha0,h_alpha0,s7,sub7⟩ := right_read _ _ _ s6
  have inc7 := fun frame member => inc6 frame (sub7 frame member)
  obtain ⟨folds,h_folds,s8,sub8⟩ := right_read _ _ _ s7
  have inc8 := fun frame member => inc7 frame (sub8 frame member)
  rw [erase_lift] at h_folds
  have folds_eq : folds = 2#usize := by
    rw [variant] at h_folds
    simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
      transport.Variant.read_discriminant] at h_folds
    exact h_folds.symm
  subst folds
  obtain ⟨capacity,h_capacity,s9,sub9⟩ := right_read _ _ _ s8
  have inc9 := fun frame member => inc8 frame (sub9 frame member)
  obtain ⟨root,h_root,s10,sub10⟩ := right_read _ _ _ s9
  have inc10 := fun frame member => inc9 frame (sub10 frame member)
  obtain ⟨rootSlice,h_rootSlice,s11,sub11⟩ := right_read _ _ _ s10
  have inc11 := fun frame member => inc10 frame (sub11 frame member)
  obtain ⟨bytes1,h_bytes1,s12,sub12⟩ := right_read _ _ _ s11
  have inc12 := fun frame member => inc11 frame (sub12 frame member)
  obtain ⟨bytes2,h_bytes2,s13,sub13⟩ := right_read _ _ _ s12
  have inc13 := fun frame member => inc12 frame (sub13 frame member)
  rw [erase_lift] at h_capacity h_root h_rootSlice h_bytes1 h_bytes2
  have rootSliceEq : rootSlice = Array.to_slice root := (Result.ok.inj h_rootSlice).symm
  subst rootSlice
  obtain ⟨a,ha,hk,sub⟩ := AuS1_Trace.success_bind _ _ _ s13
  have contains := left_read _ _ _ s13
  refine ⟨alpha0.2,a.2,root,bytes1,bytes2,a.1,h_root,h_bytes1,h_bytes2,ha,?_⟩
  intro frame member
  exact inc13 frame (contains frame member)

#print axioms reached
end AspisR1.AuS1_Row30
end
