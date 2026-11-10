-- PCVQ_ item (5). CLASS: ReviewedTranscription. HAND transcription of the derived Clone and PartialEq on M31, CM31, QM31 and WideExact.
-- Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:
--   crates/aspis-core/src/field.rs:22      #[derive(Clone, Copy, PartialEq, Eq, Debug, Default)] pub struct M31(pub u32);
--   crates/aspis-core/src/field.rs:254     #[derive(Clone, Copy, PartialEq, Eq, Debug, Default)] pub struct CM31 { pub a: M31, pub b: M31 }
--   crates/aspis-core/src/field.rs:431     #[derive(Clone, Copy, PartialEq, Eq, Debug, Default)] pub struct QM31 { pub c0: CM31, pub c1: CM31 }
--   crates/aspis-core/src/field/wide_exact.rs:27   #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)] pub struct WideExact { c0: QM31, c1: QM31 }
-- Semantics transcribed: derived Clone is field-wise clone; derived PartialEq is the conjunction of field-wise equality in declaration order.
-- Carriers are the gate types; M31 is the gate's U32.
import Aeneas
import PRVEq_Tx2Deployed_n1
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace PCVQ_DeriveRef
open AspisR1Stage2

abbrev M31 := aspis_core.field.M31
abbrev CM31 := aspis_core.field.CM31
abbrev QM31 := aspis_core.field.QM31
abbrev WE := aspis_core.field.wide_exact.WideExact

-- field.rs:22 (M31 over u32)
def m31_clone (x : M31) : Result M31 := ok x
def m31_eq (x y : M31) : Bool := x == y
-- field.rs:254
def cm31_clone (x : CM31) : Result CM31 := do
  let a ← m31_clone x.a
  let b ← m31_clone x.b
  ok ⟨a, b⟩
def cm31_eq (x y : CM31) : Bool := m31_eq x.a y.a && m31_eq x.b y.b
-- field.rs:431
def qm31_clone (x : QM31) : Result QM31 := do
  let c0 ← cm31_clone x.c0
  let c1 ← cm31_clone x.c1
  ok ⟨c0, c1⟩
def qm31_eq (x y : QM31) : Bool := cm31_eq x.c0 y.c0 && cm31_eq x.c1 y.c1
-- wide_exact.rs:27
def we_clone (x : WE) : Result WE := do
  let c0 ← qm31_clone x.c0
  let c1 ← qm31_clone x.c1
  ok ⟨c0, c1⟩
def we_eq (x y : WE) : Bool := qm31_eq x.c0 y.c0 && qm31_eq x.c1 y.c1

theorem cm31_clone_id (x : CM31) : cm31_clone x = ok x := by cases x; rfl
theorem qm31_clone_id (x : QM31) : qm31_clone x = ok x := by
  cases x with | mk c0 c1 => simp only [qm31_clone, cm31_clone_id, bind_tc_ok]
theorem we_clone_id (x : WE) : we_clone x = ok x := by
  cases x with | mk c0 c1 => simp only [we_clone, qm31_clone_id, bind_tc_ok]

/-- The deployed clone slot (yDep, NIL_FreshOps.resume) is the transcription. -/
theorem deployed_qm31_clone : (fun x : QM31 => (ok x : Result QM31)) = qm31_clone :=
  funext fun x => (qm31_clone_id x).symm

theorem m31_eq_iff (x y : M31) : m31_eq x y = true ↔ x = y := by simp [m31_eq]
theorem cm31_eq_iff (x y : CM31) : cm31_eq x y = true ↔ x = y := by
  cases x; cases y; simp [cm31_eq, m31_eq_iff]
theorem qm31_eq_iff (x y : QM31) : qm31_eq x y = true ↔ x = y := by
  cases x; cases y; simp [qm31_eq, cm31_eq_iff]
theorem we_eq_iff (x y : WE) : we_eq x y = true ↔ x = y := by
  cases x; cases y; simp [we_eq, qm31_eq_iff]

#print axioms deployed_qm31_clone
#print axioms we_clone_id
#print axioms qm31_eq_iff
#print axioms we_eq_iff
end PCVQ_DeriveRef
