import FIw_WordValue
import FIq_Native10
set_option autoImplicit false
namespace AspisR1.FIx_PathIndices
open Aeneas Aeneas.Std Result FIq_Native

theorem first (lane i : Usize) (run : 1#usize+lane=ok i) : i.val=1+lane.val := by
  have v := FIw_WordValue.add 1#usize lane i run
  exact v

theorem rate (lane i : Usize) (run : poseidon2.RATE+lane=ok i) : i.val=8+lane.val := by
  have v := FIw_WordValue.add poseidon2.RATE lane i run
  rw [poseidon2.RATE] at v
  exact v

theorem digest (i : Usize) (run : 1#usize+poseidon2.DIGEST_ELEMS=ok i) : i.val=9 := by
  have v := FIw_WordValue.add 1#usize poseidon2.DIGEST_ELEMS i run
  rw [poseidon2.DIGEST_ELEMS] at v
  exact v

theorem final (lane base i : Usize) (baseValue : base.val=9)
    (run : base+lane=ok i) : i.val=9+lane.val := by
  have v := FIw_WordValue.add base lane i run
  rw [baseValue] at v
  exact v

theorem source_bound (lane i : Usize) (hl : lane.val<8) (h : i.val=1+lane.val) : i.val<(16#usize).val := by
  rw [h]
  change 1+lane.val<16
  omega

theorem rate_bound (lane i : Usize) (hl : lane.val<8) (h : i.val=8+lane.val) : i.val<(16#usize).val := by
  rw [h]
  change 8+lane.val<16
  omega

theorem first_bound (lane i : Usize) (hl : lane.val<8) (h : i.val=1+lane.val) : i.val<(17#usize).val := by
  rw [h]
  change 1+lane.val<17
  omega

theorem last_bound (lane i : Usize) (hl : lane.val<8) (h : i.val=9+lane.val) : i.val<(17#usize).val := by
  rw [h]
  change 9+lane.val<17
  omega
#print axioms first
#print axioms rate
#print axioms digest
#print axioms final
#print axioms source_bound
#print axioms rate_bound
#print axioms first_bound
#print axioms last_bound
end AspisR1.FIx_PathIndices
