import R1Z.PV_Inv_NativeScalar
set_option autoImplicit false
namespace R1Z.PV_Inv_NativeDenominator
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitM31Ops48
local instance : DecidableEq U32 := Classical.decEq _

def loop (i : U32) : U32 → List U32 → Result U32
 | d,[] => ok d
 | d,j::js => if i=j then loop i d js else do
    let difference ← field.M31.sub i j
    let next ← field.M31.mul d difference
    loop i next js

theorem preserves (i d : U32) (js : List U32) (hi : canonical i)
    (hd : decode d ≠ 0) (hj : ∀ j ∈ js, canonical j) :
    ∃ z : U32, loop i d js=ok z ∧ decode z ≠ 0 := by
  induction js generalizing d with
  | nil => exact ⟨d,rfl,hd⟩
  | cons j js ih =>
    have hcan : canonical j := hj j (by simp)
    have htail : ∀ k ∈ js, canonical k := fun k hk => hj k (by simp [hk])
    by_cases he : i=j
    · simpa only [loop,he,if_true] using ih d hd htail
    · obtain ⟨diff,hs,hcs,hns⟩ := PV_Inv_NativeScalar.sub_nonzero i j hi hcan he
      obtain ⟨next,hm,hcm,hnm⟩ := PV_Inv_NativeScalar.mul_nonzero d diff hd hns
      obtain ⟨z,hz,hnz⟩ := ih next hnm htail
      refine ⟨z,?_,hnz⟩
      simp only [loop,he,if_false,hs,hm,bind_tc_ok,hz]

#print axioms preserves
end R1Z.PV_Inv_NativeDenominator
