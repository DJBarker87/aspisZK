import RPu_FIw_ScalarArithmetic
import ExtractedMaskM31AddSub
import RPu_FIw_WordValue
set_option autoImplicit false
namespace AspisR1.FIy_DigestTarget
open Aeneas Aeneas.Std Result FIq_Native

def run (lane : Usize) (expected : U32) (right : Bool) : Result U32 := do
  if right then do
    let i ← lane+1#usize
    if i=poseidon2.DIGEST_ELEMS then
      field.M31.add expected poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
    else ok expected
  else ok expected

def value (lane : Nat) (expected : U32) (right : Bool) : Nat :=
  if right=true ∧ lane=7 then (expected.val+1095962629)%FIw_ScalarArithmetic.P else expected.val

theorem value_exact (lane : Usize) (expected target : U32) (right : Bool)
    (hl : lane.val<8) (he : expected.val<FIw_ScalarArithmetic.P)
    (success : run lane expected right=ok target) :
    target.val<FIw_ScalarArithmetic.P ∧ target.val=value lane.val expected right := by
  cases right with
  | false=>
    simp only [run,Bool.false_eq_true,↓reduceIte] at success
    cases Result.ok.inj success
    exact ⟨he,by simp [value]⟩
  | true=>
    simp only [run,↓reduceIte] at success
    obtain ⟨i,hi,success⟩ := FIv_Map.bind_success _ _ _ success
    have vi := FIw_WordValue.add lane 1#usize i hi
    change i.val=lane.val+1 at vi
    split at success
    next eq=>
      have ie : i.val=8 := by rw [eq,poseidon2.DIGEST_ELEMS];rfl
      have lane7 : lane.val=7 := by omega
      have spec := ExtractedMaskM31AddSub.current_add_mod expected poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK he
        (by rw [poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK];decide)
      obtain ⟨out,hr,hv,hc⟩ := spec
      rw [FIv_NativeArithmetic.m31_add] at success
      have same := Result.ok.inj (hr.symm.trans success)
      subst out
      refine ⟨hc,?_⟩
      rw [hv]
      simp only [value,lane7,and_self,↓reduceIte,poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK]
      rfl
    next ne=>
      cases Result.ok.inj success
      have laneNot7 : lane.val≠7 := by
        intro h7
        apply ne
        apply UScalar.eq_of_val_eq
        rw [poseidon2.DIGEST_ELEMS]
        change i.val=8
        omega
      exact ⟨he,by simp [value,laneNot7]⟩
#print axioms value_exact
end AspisR1.FIy_DigestTarget
