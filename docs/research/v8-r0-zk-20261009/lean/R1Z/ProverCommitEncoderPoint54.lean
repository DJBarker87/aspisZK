import R1Z.ProverCommitEncoderPower54
import R1Z.ProverCommitEncoderReverse54
/-! Exact source point exponent and generator, without a supplied point image. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderPoint54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49 AspisV5FriBitReverse

def generator : Old.C := ⟨2#u32,1268011823#u32⟩
def one : Old.C := ⟨1#u32,0#u32⟩

theorem generator_canonical : Canonical generator := by
  change (2#u32).val<2147483647 ∧ (1268011823#u32).val<2147483647
  decide

theorem one_canonical : Canonical one := by
  change (1#u32).val<2147483647 ∧ (0#u32).val<2147483647
  decide

theorem one_value : value one=1 := rfl

attribute [local irreducible] source

theorem exact_result (j : Usize) :
    ∃ z : Old.C, nodes54.point j=ok (source z) ∧ Canonical z ∧
      value z=value generator^(1024+4096*reverseBits 18 j.val) := by
  obtain ⟨r,hr,hrv⟩ := ProverCommitEncoderReverse54.exact_result 18 (by decide) 18#u8 rfl j
  have hbound : r.val<262144 := by
    rw [hrv];exact reverseBits_lt_two_pow 18 j.val
  let exp := U64.wrapping_add 1024#u64 (U64.wrapping_mul 4096#u64 (UScalar.cast .U64 r))
  have he : exp.val=1024+4096*reverseBits 18 j.val := by
    have hc : (UScalar.cast .U64 r).val=r.val := by scalar_tac
    have hm : (U64.wrapping_mul 4096#u64 (UScalar.cast .U64 r)).val=4096*r.val := by
      rw [U64.wrapping_mul_val_eq,hc,show (4096#u64).val=4096 from rfl,
        show UScalar.size .U64=2^64 by rw [UScalar.size_def];rfl]
      change (4096*r.val)%2^64=4096*r.val
      apply Nat.mod_eq_of_lt
      omega
    dsimp only [exp]
    rw [U64.wrapping_add_val_eq,hm,show (1024#u64).val=1024 from rfl,
      show UScalar.size .U64=2^64 by rw [UScalar.size_def];rfl]
    change (1024+4096*r.val)%2^64=1024+4096*reverseBits 18 j.val
    rw [Nat.mod_eq_of_lt (by omega),hrv]
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitEncoderPower54.exact_result
    (1024+4096*reverseBits 18 j.val) exp he generator one generator_canonical one_canonical
  refine ⟨z,?_,hcz,?_⟩
  · rw [nodes54.point,hr]
    simp only [nodes54.point,field.CM31.new,lift,bind_tc_ok]
    simpa only [source,ProverCommitRelease47.convC,ProverCommitPrimitive47.fromC,
      generator,one,field.CM31.ONE] using hz
  · rw [hdz,one_value,one_mul]

#print axioms generator_canonical
#print axioms one_canonical
#print axioms one_value
#print axioms exact_result
end R1Z.ProverCommitEncoderPoint54
