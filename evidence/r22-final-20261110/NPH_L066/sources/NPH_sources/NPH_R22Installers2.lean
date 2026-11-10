import NJJ_QueryOps
import SAQ_LineQuery
import RPz7_FIp_Install

/-! NPH_ (R22, task 2): the four query installers named in section 14 as Lean statements.
The CW-executing query slots are op2 (wide add), op3 (mixed mulE), op9 (mulK), op16 (line),
op17 (circle) and op20 (dots). For each installer, every slot it sets is definitionally the
NJJ_QueryOps.concrete slot, and every other slot is passed through unchanged (rfl):
- NFS_QueryOps.base sets op16 only;
- SAQ_QuerySource.install sets op2, op3, op9 (through SAQ_Arithmetic.install) and the
  scalar slots op4..op8 (SAQ_Query.install);
- SAQ_LineQuery.install is SAQ_QuerySource.install followed by op16;
- FIp_Install.select sets the query op17, op20 and widePartialEq and the boundaries
  mask/add/mul (FIp_SemanticArithmetic), and keeps every other query slot.
Each installer applied to NJJ_QueryOps.concrete returns NJJ_QueryOps.concrete (rfl), and the
SAQ installers return the concrete CW slots on EVERY input record. This replaces the source
reading of section 14; it is a definitional statement, not a new semantic claim. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Installers2
open Aeneas Aeneas.Std Result
open Port3_NativeQueryBody

abbrev C := NJJ_QueryOps.concrete

theorem nfs_base_slots (ops : Ops) :
    (NFS_QueryOps.base ops).op16 = C.op16 ∧ (NFS_QueryOps.base ops).op2 = ops.op2 ∧
    (NFS_QueryOps.base ops).op3 = ops.op3 ∧ (NFS_QueryOps.base ops).op9 = ops.op9 ∧
    (NFS_QueryOps.base ops).op17 = ops.op17 ∧ (NFS_QueryOps.base ops).op20 = ops.op20 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms nfs_base_slots

theorem nfs_base_concrete : NFS_QueryOps.base C = C := rfl
#print axioms nfs_base_concrete

theorem saq_source_slots (ops : Ops) :
    (SAQ_QuerySource.install ops).op2 = C.op2 ∧ (SAQ_QuerySource.install ops).op3 = C.op3 ∧
    (SAQ_QuerySource.install ops).op9 = C.op9 ∧ (SAQ_QuerySource.install ops).op4 = C.op4 ∧
    (SAQ_QuerySource.install ops).op5 = C.op5 ∧ (SAQ_QuerySource.install ops).op6 = C.op6 ∧
    (SAQ_QuerySource.install ops).op7 = C.op7 ∧ (SAQ_QuerySource.install ops).op8 = C.op8 ∧
    (SAQ_QuerySource.install ops).op16 = ops.op16 ∧ (SAQ_QuerySource.install ops).op17 = ops.op17 ∧
    (SAQ_QuerySource.install ops).op20 = ops.op20 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms saq_source_slots

theorem saq_source_concrete : SAQ_QuerySource.install C = C := rfl
#print axioms saq_source_concrete

theorem saq_line_slots (ops : Ops) :
    (SAQ_LineQuery.install ops).op2 = C.op2 ∧ (SAQ_LineQuery.install ops).op3 = C.op3 ∧
    (SAQ_LineQuery.install ops).op9 = C.op9 ∧ (SAQ_LineQuery.install ops).op16 = C.op16 ∧
    (SAQ_LineQuery.install ops).op17 = ops.op17 ∧ (SAQ_LineQuery.install ops).op20 = ops.op20 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms saq_line_slots

theorem saq_line_concrete : SAQ_LineQuery.install C = C := rfl
#print axioms saq_line_concrete

theorem fip_select_slots {E : Type} (r : NP6_StdModel.Reservation)
    (c : DrvC_Installation.Configuration FIo_Install.W E) :
    (FIp_Install.select r c).query.op17 = C.op17 ∧ (FIp_Install.select r c).query.op20 = C.op20 ∧
    (FIp_Install.select r c).query.widePartialEq = C.widePartialEq ∧
    (FIp_Install.select r c).query.op2 = c.query.op2 ∧ (FIp_Install.select r c).query.op3 = c.query.op3 ∧
    (FIp_Install.select r c).query.op9 = c.query.op9 ∧ (FIp_Install.select r c).query.op16 = c.query.op16 ∧
    (FIp_Install.select r c).boundaries.mask = FIp_SemanticArithmetic.mask ∧
    (FIp_Install.select r c).boundaries.add = FIp_SemanticArithmetic.add ∧
    (FIp_Install.select r c).boundaries.mul = FIp_SemanticArithmetic.mul :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms fip_select_slots

/-- On a configuration whose query record is the concrete one, FIp_Install.select keeps it. -/
theorem fip_select_concrete {E : Type} (r : NP6_StdModel.Reservation)
    (c : DrvC_Installation.Configuration FIo_Install.W E) (h : c.query = C) :
    (FIp_Install.select r c).query = C := by
  show { c.query with op20 := FIp_DotsAdapter.dots, op17 := FIp_CircleQuery.circle,
    widePartialEq := FIp_Equality.dictionary } = C
  rw [h]
  rfl
#print axioms fip_select_concrete

end AspisR1.NPH_R22Installers2
