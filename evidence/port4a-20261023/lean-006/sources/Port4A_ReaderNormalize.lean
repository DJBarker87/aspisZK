import Port4A_NativeReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_ReaderNormalize
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem checked_sub (x y : Usize) (order : y.val≤x.val) :
    (x-y : Result Usize)=ok (Usize.wrapping_sub x y) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=x) (y:=y) order)
  have same : z=Usize.wrapping_sub x y := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_sub_val_eq]
    have capacity : x.val<UScalar.size .Usize := by
      simpa only [UScalar.size] using x.hBounds
    have eq : x.val+(UScalar.size .Usize-y.val) =
        (x.val-y.val)+UScalar.size .Usize := by omega
    rw [eq,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
    exact hv.1.trans (Nat.mod_eq_of_lt (by omega)).symm
  exact hz.trans (congrArg Result.ok same)

/-- Full Result equality, including rejected prefixes. Only the local size
leaf's numerical lower bound is required; it contains no reader output law. -/
theorem source (ops : ResumeOps)
    (sizeBound : ∀ v n, ops.checkpointSize v=ok n → 32≤n.val)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (bytes proof pub : Slice U8) (v : transport.Variant) :
    Port4A_NativeReader.resume ops D bytes proof pub v hash =
      verifier.resumeWithOps ops D bytes proof pub v hash := by
  rw [← CheckpointBytes5Resume.source]
  have tailEq : ∀ i4 end1 s6 a2,
      Port4A_NativeReader.tail ops bytes v i4 end1 s6 a2 =
        CheckpointBytes5Resume.tail ops bytes v i4 end1 s6 a2 := by
    intros; rfl
  unfold Port4A_NativeReader.resume
  simp only [CheckpointBytes5Resume.program,CheckpointBytes5Effect.erase_bind,
    CheckpointBytes5Effect.erase_lift,CheckpointBytes5Effect.erase_read,
    CheckpointBytes5Effect.erase_pure,CheckpointBytes5Effect.erase_ite]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro size hsize
  by_cases same : Slice.len bytes = size
  · have order : (32#usize : Usize).val≤(Slice.len bytes).val := by
      rw [same]; exact sizeBound v size hsize
    rw [checked_sub _ _ order]
    simp only [tailEq]
    rfl
  · simp only [bne_iff_ne,same,not_false_eq_true,if_true]

#print axioms checked_sub
#print axioms source
end AspisR1.Port4A_ReaderNormalize
end
