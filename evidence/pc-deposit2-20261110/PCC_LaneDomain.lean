import PCC_LaneReference
set_option autoImplicit false
namespace PCC
open PCA

theorem lane_word_bound (commitment : Digest) :
    commitment[0].toNat % 256 % 8 < 8 := Nat.mod_lt _ (by decide)

theorem lane_on_canonical (commitment : Digest) (s : PCA_State)
    (h : canonical commitment = true) :
    (laneReference commitment s).reply =
      .ok (UInt8.ofNat (commitment[0].toNat % 256 % 8)) := by
  simp only [laneReference, h, Bool.true_eq, ↓reduceIte]

#print axioms lane_word_bound
#print axioms lane_on_canonical
end PCC
