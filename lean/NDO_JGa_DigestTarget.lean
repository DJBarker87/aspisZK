import RPv_JFy_Steps
import RPv_FIy_DigestTarget
set_option autoImplicit false
namespace AspisR1.JGa_DigestTarget
open Aeneas Aeneas.Std Result WP FIq_Native

@[step] theorem source (lane : Usize) (expected : U32) (right : Bool)
    (hl : lane.val<8) (he : expected.val<FIw_ScalarArithmetic.P) :
    FIy_DigestTarget.run lane expected right ⦃ out => out.val<FIw_ScalarArithmetic.P ⦄ := by
  apply exists_imp_spec
  cases right with
  | false => exact ⟨expected,rfl,he⟩
  | true =>
    obtain ⟨i,hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=lane) (y:=1#usize) (by scalar_tac))
    unfold FIy_DigestTarget.run
    simp only [Bool.true_eq, ↓reduceIte]
    rw [hi,bind_tc_ok]
    split
    · obtain ⟨out,ho,hv,hc⟩ := ExtractedMaskM31AddSub.current_add_mod expected poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK he
        (by rw [poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK];decide)
      exact ⟨out,by rw [FIv_NativeArithmetic.m31_add,ho],hc⟩
    · exact ⟨expected,rfl,he⟩
#print axioms source
end AspisR1.JGa_DigestTarget
