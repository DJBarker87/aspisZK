import PV_L2C_PathRange
import PV_L2C_ValueRange
import PV_L2C_OccRange
import PV_L2C_ChunkRange
set_option autoImplicit false
namespace PV_L2C_AuxRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

theorem inverse (x : U32) : (invR x).val < 2147483647 := by
  change (BitVec.ofNat 32 (x.val^2147483645%2147483647)).toNat < 2147483647
  have hm := Nat.mod_lt (x.val^2147483645) (by omega : 0 < 2147483647)
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact hm
#print axioms inverse

theorem input (w : RustWitness) (hw : R1Z.BuilderRecordCanonical.CanonicalWords w) :
    PV_L2C_OccRange.Fields (inRec w) := by
  refine ⟨hw.pairOccupied,hw.pairInverse,hw.pairSecond,?_⟩
  intro h
  have hb := hw.shape.bits 0 (by omega)
  change (w.bits.val[0]!).val < 2147483647
  omega
#print axioms input

theorem output (w : RustWitness) (p : RustPublic) : PV_L2C_OccRange.Fields (outRec w p) := by
  unfold outRec
  cases p.variant
  · refine ⟨by scalar_tac,inverse _,?_,by intro h;cases h⟩
    exact PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.note _ _)
  · exact ⟨by scalar_tac,by scalar_tac,zero8_canon,by intro h;cases h⟩
#print axioms output

theorem aux (w : RustWitness) (p : RustPublic)
    (hw : R1Z.BuilderRecordCanonical.CanonicalWords w)
    (b : Array U32 256#usize) (hb : auxR w p = ok b) : Canonical b := by
  unfold auxR R0WriterCopies.write_aux_block at hb
  pv_peel hb with values hv
  pv_peel hb with first hf
  apply PV_L2C_OccRange.row first _ 10#usize (by scalar_tac) (outRec w p) (output w p) b hb
  apply PV_L2C_OccRange.row values _ 9#usize (by scalar_tac) (inRec w) (input w hw) first hf
  apply PV_L2C_ValueRange.block _ _ values hv
  intro j hj
  interval_cases j
  · exact hw.shape.values.1
  · exact hw.shape.values.2.1
  · exact hw.shape.values.2.2
#print axioms aux

theorem path (w : RustWitness) (p : RustPublic) (hw : WitnessOk w)
    (b : Array U32 1536#usize) (hb : pathR w p = ok b) : Canonical b := by
  unfold pathR R0WriterCopies.write_path_block at hb
  apply PV_L2C_PathRange.loop w.bits (curArr w p) (leftArr w p) (rightArr w p)
    _ _ _ _ 24 0#usize _ b (by scalar_tac) (zeros 1536#usize) hb
  · intro j hj
    have hbits := hw.bits j hj
    omega
  · intro j hj
    rw [curArr,arr24_get _ j hj]
    exact PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.tree w p _)
  · intro j hj
    rw [leftArr,arr24_get _ j hj]
    exact (PV_L2C_ChunkRange.ordered _ _ _
      (PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.tree w p _)) (hw.sibs j hj)).1
  · intro j hj
    rw [rightArr,arr24_get _ j hj]
    exact (PV_L2C_ChunkRange.ordered _ _ _
      (PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.tree w p _)) (hw.sibs j hj)).2
#print axioms path
end PV_L2C_AuxRange
