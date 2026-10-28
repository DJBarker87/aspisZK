import R1Z.PV_RDCD3_V260Owned
import R1Z.PV_RDCD3_V260RowResult
import R1Z.PV_RDCD3_ReadHoist

namespace R1Z.PV_RDCD3_V260Exact
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_B2_253c1
abbrev K := aspis_core.field.QM31

/-- The native outer factor read stays inside every original fold iteration. -/
def tensor (w : host_weights.Weights) (kind j : Usize) : Result K := do
  let k ← if kind < 4#usize then ok (Usize.wrapping_sub kind 1#usize)
          else ok (Usize.wrapping_sub kind 2#usize)
  PV_RDCD3_RangeLoop.source (fun v d => do
    let factors ← Array.index_usize w.factors k
    PV_RDCD3_V260Folds.tensorStep factors j v d) ⟨0,5⟩ aspis_core.field.QM31.ONE

def point (w : host_weights.Weights) (kind j : Usize) : Result K := do
  let r ← host_weights.host_row w.variant j
  PV_RDCD3_RangeLoop.source (fun v b => do
    let points ← Array.index_usize w.points (Usize.wrapping_sub kind 1#usize)
    PV_RDCD3_V260Folds.pointStep points r v b) ⟨0,10⟩ aspis_core.field.QM31.ONE

/-- Preserve inactive's explicit invalid-row rejection through native unwrap;
complete row lookup will prove the panic branch unreachable after success. -/
def inactive (w : host_weights.Weights) (j : Usize) : Result K := do
  let r ← host_weights.host_row w.variant j
  if r.val < 1024 then
    let row ← r / 16#usize
    let mask ← Array.index_usize aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS row
    let bit ← r % 16#usize
    if (U16.wrapping_shr mask (UScalar.cast .U32 bit) &&& 1#u16)=0#u16
    then ok aspis_core.field.QM31.ONE else ok aspis_core.field.QM31.ZERO
  else fail .panic

theorem tensor_refactor (w : host_weights.Weights) (kind j : Usize) :
    tensor w kind j = PV_RDCD3_V260Owned.tensor w kind j := by
  unfold tensor PV_RDCD3_V260Owned.tensor
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro k _
  exact PV_RDCD3_ReadHoist.loop_nonempty (Array.index_usize w.factors k)
    (fun factors => PV_RDCD3_V260Folds.tensorStep factors j) 5 _ (by omega)

theorem point_refactor (w : host_weights.Weights) (kind j : Usize) :
    point w kind j = PV_RDCD3_V260Owned.point w kind j := by
  unfold point PV_RDCD3_V260Owned.point
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r _
  exact PV_RDCD3_ReadHoist.loop_nonempty
    (Array.index_usize w.points (Usize.wrapping_sub kind 1#usize))
    (fun points => PV_RDCD3_V260Folds.pointStep points r) 10 _ (by omega)

theorem inactive_refactor (w : host_weights.Weights) (j : Usize) :
    inactive w j = PV_RDCD3_V260Owned.inactive w j := by
  rcases PV_RDCD3_V260RowResult.complete w.variant j with ⟨r,hr,hi⟩ | hf
  · simp only [inactive,PV_RDCD3_V260Owned.inactive,hr,bind_tc_ok,hi,if_true]
  · simp only [inactive,PV_RDCD3_V260Owned.inactive,hf,bind_tc_fail]

def original (w : host_weights.Weights) (kind j : Usize) : Result K :=
  if kind=0#usize then inactive w j
  else if kind=4#usize then PV_RDCD3_V260Owned.extra w j
  else if kind≥1#usize ∧ kind≤3#usize ∧ PV_RDCD3_V260Owned.isD w.variant=true then point w kind j
  else tensor w kind j

theorem refactor (w : host_weights.Weights) (kind j : Usize) :
    original w kind j = PV_RDCD3_V260Owned.original w kind j := by
  simp only [original,PV_RDCD3_V260Owned.original,inactive_refactor,point_refactor,tensor_refactor]

/-- Complete source-shaped Result statement. Source binding and existing tool
trust are recorded separately; this theorem removes no endpoint premise. -/
theorem source (w : host_weights.Weights) (kind j : Usize) :
    host_weights.raw_value w kind j = original w kind j :=
  (PV_RDCD3_V260Owned.source w kind j).trans (refactor w kind j).symm

#print axioms tensor_refactor
#print axioms point_refactor
#print axioms inactive_refactor
#print axioms refactor
#print axioms source
end R1Z.PV_RDCD3_V260Exact
