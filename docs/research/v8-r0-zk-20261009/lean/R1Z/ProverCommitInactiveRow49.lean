import R1Z.ProverCommitInactiveSource49
import D18Transport
import R1Z.ProverCommitBasisFillValue47
/-! Exact scalar semantics of the closed-form owned S2 row permutation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitInactiveRow49
open Aeneas Aeneas.Std Result AspisR1InactiveOwner49

theorem mul_val (x y : Usize) (h : x.val*y.val<2048) :
    (Usize.wrapping_mul x y).val=x.val*y.val := by
  rw [Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  have hs : 2048≤UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact le_trans (by decide : 2048≤2^32) (Nat.pow_le_pow_right (by decide) System.Platform.le_numBits)
  omega

theorem div_value (x d : Usize) (hd : d.val≠0) :
    ∃ z : Usize, x/d=ok z ∧ z.val=x.val/d.val := by
  obtain ⟨z,hz,hv,_⟩ := UScalar.div_bv_spec x hd
  exact ⟨z,hz,hv⟩

theorem rem_value (x d : Usize) (hd : d.val≠0) :
    ∃ z : Usize, x%d=ok z ∧ z.val=x.val%d.val := by
  exact WP.spec_imp_exists (UScalar.rem_spec x hd)

theorem row_exact (j : Usize) : ∃ r : Usize, owned.row j=ok r ∧ r.val=AspisR1.rowNat j.val := by
  obtain ⟨a0,ha0,hva0⟩ := div_value j 64#usize (by decide)
  obtain ⟨a,ha,hva⟩ := rem_value a0 4#usize (by decide)
  obtain ⟨b0,hb0,hvb0⟩ := div_value j 256#usize (by decide)
  obtain ⟨b,hb,hvb⟩ := rem_value b0 4#usize (by decide)
  obtain ⟨c0,hc0,hvc0⟩ := div_value j 16#usize (by decide)
  obtain ⟨c,hc,hvc⟩ := rem_value c0 4#usize (by decide)
  obtain ⟨d,hd,hvd⟩ := rem_value j 4#usize (by decide)
  obtain ⟨e0,he0,hve0⟩ := div_value j 4#usize (by decide)
  obtain ⟨e,he,hve⟩ := rem_value e0 4#usize (by decide)
  have hla : a.val<4 := by rw [hva];exact Nat.mod_lt _ (by decide)
  have hlb : b.val<4 := by rw [hvb];exact Nat.mod_lt _ (by decide)
  have hlc : c.val<4 := by rw [hvc];exact Nat.mod_lt _ (by decide)
  have hld : d.val<4 := by rw [hvd];exact Nat.mod_lt _ (by decide)
  have hle : e.val<4 := by rw [hve];exact Nat.mod_lt _ (by decide)
  let b4 := Usize.wrapping_mul 4#usize b
  let c16 := Usize.wrapping_mul 16#usize c
  let d64 := Usize.wrapping_mul 64#usize d
  let e256 := Usize.wrapping_mul 256#usize e
  have vb : b4.val=4*b.val := mul_val _ _ (by change 4*b.val<2048;omega)
  have vc : c16.val=16*c.val := mul_val _ _ (by change 16*c.val<2048;omega)
  have vd : d64.val=64*d.val := mul_val _ _ (by change 64*d.val<2048;omega)
  have ve : e256.val=256*e.val := mul_val _ _ (by change 256*e.val<2048;omega)
  let ab := Usize.wrapping_add a b4
  have vab : ab.val=a.val+4*b.val := by
    rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [vb];omega),vb]
  let abc := Usize.wrapping_add ab c16
  have vabc : abc.val=a.val+4*b.val+16*c.val := by
    rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [vab,vc];omega),vab,vc]
  let abcd := Usize.wrapping_add abc d64
  have vabcd : abcd.val=a.val+4*b.val+16*c.val+64*d.val := by
    rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [vabc,vd];omega),vabc,vd]
  let r := Usize.wrapping_add abcd e256
  have vr : r.val=a.val+4*b.val+16*c.val+64*d.val+256*e.val := by
    rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [vabcd,ve];omega),vabcd,ve]
  refine ⟨r,?_,?_⟩
  · simp only [owned.row,ha0,ha,hb0,hb,hc0,hc,hd,he0,he,lift,bind_tc_ok]
    rfl
  · rw [vr,hva,hvb,hvc,hvd,hve,hva0,hvb0,hvc0,hve0]
    change j.val/64%4+4*(j.val/256%4)+16*(j.val/16%4)+64*(j.val%4)+256*(j.val/4%4)=_
    unfold AspisR1.rowNat
    omega

#print axioms mul_val
#print axioms div_value
#print axioms rem_value
#print axioms row_exact
end R1Z.ProverCommitInactiveRow49
