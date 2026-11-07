import LIB_Instances
set_option autoImplicit false
noncomputable section
namespace LIB_ParseShape094
open RSL
/-- The SAME arguments rejected by frozen parse_shape reach no suffix call. -/
theorem rejected (a : TX1_094.Args LIB_Instances.VL) (env : Env)
 (hk : a.k = SPLIT) (hlen : a.proof.length ≠ 57607)
 (o : Obs (Except LIB_Instances.VL.VErr Bytes)) :
 TX1_094.Ref LIB_Instances.VL LIB_Instances.P a env o ↔
 o = ⟨.ret (.error LIB_Instances.VL.vParse),[]⟩ := by
 unfold TX1_094.Ref
 have guard : (a.k != SPLIT) = false := by simp only [hk,bne_self_eq_false]
 rw [guard,RE.check_false,RE.seq_pure]
 unfold RE.seq
 rw [RE.bind]
 rw [Spec.bind_det _ _ env _ (LIB_ParseShapeTotal.rejected a.proof env hlen)]
 rfl
/-- Replacement for the old empty-proof contradiction: an actual reference
observation exists with proof.length=0 at every public value and Env. -/
theorem empty_reference (pub : LIB_Instances.VL.Public) (env : Env) :
 TX1_094.Ref LIB_Instances.VL LIB_Instances.P ⟨pub,[],[],10⟩ env
 ⟨.ret (.error LIB_Instances.VL.vParse),[]⟩ := by
 exact (rejected ⟨pub,[],[],10⟩ env rfl (by simp) _).mpr rfl
/-- The old required_width conclusion is false at the repaired instance. -/
theorem width_not_required (pub : LIB_Instances.VL.Public) (env : Env) :
 ∃ (a : TX1_094.Args LIB_Instances.VL) (o : Obs (Except LIB_Instances.VL.VErr Bytes)),
 a.k = SPLIT ∧ TX1_094.Ref LIB_Instances.VL LIB_Instances.P a env o ∧ a.proof.length ≠ 57607 :=
 ⟨⟨pub,[],[],10⟩,⟨.ret (.error LIB_Instances.VL.vParse),[]⟩,rfl,empty_reference pub env,by simp⟩
#print axioms rejected
#print axioms empty_reference
#print axioms width_not_required
end LIB_ParseShape094
