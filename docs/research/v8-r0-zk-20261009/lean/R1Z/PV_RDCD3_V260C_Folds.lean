import R1Z.PV_B2_C_RawWeights251Funs
import R1Z.PV_RDCD3_RangeLoop
import R1Z.PV_RDCD3_OrderedFold

namespace R1Z.PV_RDCD3_V260C_Folds
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_B2_251c1
abbrev K := aspis_core.field.QM31

/-- Finite specialization of (d,2*d) on the source's fixed 0..5 range.
The off-domain error is unreachable in tensor_loop; it carries no native credit. -/
def tensorArgs : Nat → Result (Usize × U32)
  | 0 => ok (0#usize,0#u32)
  | 1 => ok (1#usize,2#u32)
  | 2 => ok (2#usize,4#u32)
  | 3 => ok (3#usize,6#u32)
  | 4 => ok (4#usize,8#u32)
  | _ => fail .undef

def pointArgs : Nat → Result (Usize × U32)
  | 0 => ok (9#usize,0#u32)
  | 1 => ok (8#usize,1#u32)
  | 2 => ok (7#usize,2#u32)
  | 3 => ok (6#usize,3#u32)
  | 4 => ok (5#usize,4#u32)
  | 5 => ok (4#usize,5#u32)
  | 6 => ok (3#usize,6#u32)
  | 7 => ok (2#usize,7#u32)
  | 8 => ok (1#usize,8#u32)
  | 9 => ok (0#usize,9#u32)
  | _ => fail .undef

def tensorStep (factors : Array (Array K 4#usize) 5#usize) (j : Usize)
    (v : K) (d : Nat) : Result K := do
  let ds ← tensorArgs d
  let row ← Array.index_usize factors ds.1
  let q ← Array.index_usize row (Usize.wrapping_shr j ds.2 &&& 3#usize)
  aspis_core.field.QM31.mul v q

def pointStep (points : Array K 10#usize) (r : Usize) (v : K) (b : Nat) : Result K := do
  let ib ← pointArgs b
  let q ← Array.index_usize points ib.1
  let factor ← host_weights.point_factor q r ib.2
  aspis_core.field.QM31.mul v factor

/-- The actual source-shaped fold, not just an equality between two lists. -/
theorem tensor_loop (factors : Array (Array K 4#usize) 5#usize) (j : Usize) :
    PV_RDCD3_RangeLoop.source (tensorStep factors j) ⟨0,5⟩ aspis_core.field.QM31.ONE =
      host_weights.tensor_raw factors j := by
  rw [PV_RDCD3_RangeLoop.complete (tensorStep factors j) 5 0 5 _ (by omega),
    PV_RDCD3_OrderedFold.five]
  simp only [List.foldlM_cons,List.foldlM_nil,tensorStep,tensorArgs,
    host_weights.tensor_raw,bind_tc_ok,bind_assoc,bind_pure,lift]

/-- All ten coordinates, in their original order, including every Result branch. -/
theorem point_loop (points : Array K 10#usize) (r : Usize) :
    PV_RDCD3_RangeLoop.source (pointStep points r) ⟨0,10⟩ aspis_core.field.QM31.ONE =
      host_weights.point_raw points r := by
  rw [PV_RDCD3_RangeLoop.complete (pointStep points r) 10 0 10 _ (by omega),
    PV_RDCD3_OrderedFold.ten]
  simp only [List.foldlM_cons,List.foldlM_nil,pointStep,pointArgs,
    host_weights.point_raw,bind_tc_ok,bind_assoc,bind_pure,lift]

/-- The native conditional reads one point in either branch. Distributing
that immutable read through the pure bit guard preserves the complete Result. -/
theorem point_read_order (read : Result K) (r : Usize) (shift : U32) :
    (if (r &&& Usize.wrapping_shl 1#usize shift)=0#usize then
      (do let q ← read; aspis_core.field.QM31.sub aspis_core.field.QM31.ONE q)
    else read) =
    (do let q ← read; host_weights.point_factor q r shift) := by
  by_cases h : (r &&& Usize.wrapping_shl 1#usize shift)=0#usize <;>
    simp only [host_weights.point_factor,lift,bind_tc_ok,h,if_true,if_false,bind_pure]
  cases read <;> rfl
#print axioms point_read_order

#print axioms tensor_loop
#print axioms point_loop
end R1Z.PV_RDCD3_V260C_Folds
