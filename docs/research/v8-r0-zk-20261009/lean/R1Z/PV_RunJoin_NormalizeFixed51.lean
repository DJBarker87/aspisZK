import R1Z.ProverCommitNativeOps47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NormalizeFixed51
open Aeneas Aeneas.Std ProverCommitPrimitive47 ProverCommitSubfieldOps47

theorem word (x : U32) (h : x.val<2147483647) : ProverCommitNativeOps47.normalizeWord x=x := by
  apply UScalar.eq_of_val_eq
  rw [ProverCommitNativeOps47.normalize_val,Nat.mod_eq_of_lt h]

theorem fixed (q : Old.Q) (h : Canonical q) : ProverCommitNativeOps47.normalize q=q := by
  unfold ProverCommitNativeOps47.normalize
  rw [word q.c0.a h.1.1,word q.c0.b h.1.2,word q.c1.a h.2.1,word q.c1.b h.2.2]
#print axioms word
#print axioms fixed
end R1Z.PV_RunJoin_NormalizeFixed51
