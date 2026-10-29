import R1Z.PV_RunJoin_SamplerByteIndices54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerChecked54

theorem sub_one (i : Usize) (hi : Nat.lt 0 (UScalar.val i)) : i-1#usize=ok (Usize.wrapping_sub i 1#usize) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=i) (y:=1#usize) (by change Nat.le 1 (UScalar.val i);omega))
  have he : z=Usize.wrapping_sub i 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_SamplerCounters54.sub_one i hi]
    exact hv.1
  exact he ▸ hz

theorem shift32 (x : U64) : x <<< 32#i32=ok (U64.wrapping_shl x 32#u32) := rfl

theorem add (i j : Usize) (hi : i.val<32) (hj : j.val<4) :
    i+j=ok (Usize.wrapping_add i j) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x:=i) (y:=j) (by scalar_tac))
  have he : z=Usize.wrapping_add i j := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_SamplerByteIndices54.add i j hi hj]
    exact hv
  exact he ▸ hz

theorem mul4 (i : Usize) (hi : i.val<8) :
    4#usize*i=ok (Usize.wrapping_mul 4#usize i) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=4#usize) (y:=i) (by scalar_tac))
  have he : z=Usize.wrapping_mul 4#usize i := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_SamplerByteIndices54.mul4 i hi]
    exact hv
  exact he ▸ hz
#print axioms sub_one
#print axioms shift32
#print axioms add
#print axioms mul4
end R1Z.PV_RunJoin_SamplerChecked54
