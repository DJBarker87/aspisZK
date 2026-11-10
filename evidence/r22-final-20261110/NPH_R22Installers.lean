import NPH_R22Weak
import NBF_BasisInstall
import SAQ_Geometry
import SAQ_Query
import LIBC_QueryOps
import NJJ_QueryOps
import S7Kani3BasisOuter
import R17CurrentCM31Semantics

/-! NPH_ (R22, separate limb invariant, item (ii)): installer lemmas. The weak limb domain is
`W x := x.val ≤ P` (P = 2^31-1), the domain on which NPH_R22Weak proves every kernel checked-
total and closed. For each hand-written installer, every M31-level callback it installs
(constants, M31 sub/mul/add/double, S7 double/t2, the R17 M31 and CM31 operation records) maps
W inputs to an ok W output. No ops interface or merged module is changed: the invariant is a
separate statement about the installed records. Callbacks on extension/wide values
(op1-op3, op9-op21 of the query ops; op14/op15 line and point of the geometry ops) are not
covered here; see NPH_R22_STATUS.md section 10. Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Installers
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22Weak

def W (x : U32) : Prop := x.val ≤ 2147483647
def ConstW (r : Result U32) : Prop := ∃ z, r = ok z ∧ W z
def Pres1 (f : U32 → Result U32) : Prop := ∀ x, W x → ∃ z, f x = ok z ∧ W z
def Pres2 (f : U32 → U32 → Result U32) : Prop := ∀ x y, W x → W y → ∃ z, f x y = ok z ∧ W z

theorem const0 : ConstW (ok 0#u32) := ⟨_, rfl, by unfold W; first | decide | simp | scalar_tac⟩
theorem const1 : ConstW (ok 1#u32) := ⟨_, rfl, by unfold W; first | decide | simp | scalar_tac⟩

theorem QA_sub_pres : Pres2 AspisR1Qm31ArithmeticProbe.field.M31.sub := by
  intro x y hx hy; rw [QA_M31_sub_eq]; exact refSub_weak x y hx hy
theorem QA_add_pres : Pres2 AspisR1Qm31ArithmeticProbe.field.M31.add := by
  intro x y hx hy; rw [QA_M31_add_eq]; exact refAdd_weak x y hx hy
theorem QA_mul_pres : Pres2 AspisR1Qm31ArithmeticProbe.field.M31.mul := by
  intro x y _ _
  obtain ⟨z, hz, hv⟩ := refMul_total x y
  rw [QA_M31_mul_eq]; exact ⟨z, hz, by unfold W; omega⟩
theorem QA_double_pres : Pres1 AspisR1Qm31ArithmeticProbe.field.M31.double := by
  intro x hx; unfold AspisR1Qm31ArithmeticProbe.field.M31.double; exact QA_add_pres x x hx hx
theorem S7_double_pres : Pres1 S7Kani3BasisOuter.double := by
  intro x hx; unfold S7Kani3BasisOuter.double; exact QA_add_pres x x hx hx
theorem S7_t2_pres : Pres1 S7Kani3BasisOuter.t2 := by
  intro x hx
  obtain ⟨m, hm, wm⟩ := QA_mul_pres x x hx hx
  obtain ⟨m1, hm1, wm1⟩ := S7_double_pres m wm
  obtain ⟨z, hz, wz⟩ := QA_sub_pres m1 1#u32 wm1 (by unfold W; first | decide | simp | scalar_tac)
  exact ⟨z, by simp only [S7Kani3BasisOuter.t2, hm, hm1, hz, bind_tc_ok], wz⟩

/-- The M31-level callbacks of a query ops record preserve W. -/
structure QueryM31W (ops : Port3_NativeQueryBody.Ops) : Prop where
  op4 : ConstW ops.op4
  op5 : ConstW ops.op5
  op6 : Pres2 ops.op6
  op7 : Pres2 ops.op7
  op8 : Pres1 ops.op8

theorem NBF_BasisInstall_install_W (ops : Port3_NativeQueryBody.Ops) :
    QueryM31W (NBF_BasisInstall.install ops) :=
  ⟨const0, const1, QA_sub_pres, QA_mul_pres, fun x hx => QA_add_pres x x hx hx⟩
theorem SAQ_Query_install_W (ops : Port3_NativeQueryBody.Ops) :
    QueryM31W (AspisR1.SAQ_Query.install ops) :=
  ⟨const0, const1, QA_sub_pres, QA_mul_pres, S7_double_pres⟩
theorem LIBC_QueryOps_seed_W : QueryM31W LIBC_QueryOps.seed :=
  ⟨const0, const1, QA_sub_pres, QA_mul_pres, S7_double_pres⟩
theorem NJJ_QueryOps_concrete_W : QueryM31W NJJ_QueryOps.concrete :=
  ⟨const0, const1, QA_sub_pres, QA_mul_pres, S7_double_pres⟩

/-- The M31-level callbacks of a geometry ops record preserve W (op14/op15 not covered). -/
structure GeometryM31W {C : Type} (ops : Port3_NativeGeometryBody.Ops C) : Prop where
  op7 : ConstW ops.op7
  op8 : Pres2 ops.op8
  op9 : Pres2 ops.op9
  op10 : Pres1 ops.op10

theorem SAQ_Geometry_install_W {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    GeometryM31W (AspisR1.SAQ_Geometry.install ops) :=
  ⟨const1, QA_sub_pres, QA_mul_pres, QA_double_pres⟩

/-- R17 M31 operation record. -/
theorem R17_M31_operations_W :
    Pres2 R17CurrentM31Semantics.operations.mul ∧ Pres1 R17CurrentM31Semantics.operations.double ∧
      Pres2 R17CurrentM31Semantics.operations.sub :=
  ⟨QA_mul_pres, QA_double_pres, QA_sub_pres⟩

/-- R17 CM31 operation record: `new` and `mul` map W limbs to W limbs. -/
theorem R17_CM31_operations_new_W (a b : U32) (ha : W a) (hb : W b) :
    ∃ z, R17CurrentCM31Semantics.operations.new a b = ok z ∧ W z.a ∧ W z.b :=
  ⟨_, rfl, ha, hb⟩
theorem R17_CM31_operations_mul_W (a b : R17CurrentCM31Semantics.SourceCM)
    (ha : W a.a) (hb : W a.b) (hc : W b.a) (hd : W b.b) :
    ∃ z, R17CurrentCM31Semantics.operations.mul a b = ok z ∧ W z.a ∧ W z.b := by
  obtain ⟨z, hz, h1, h2⟩ := QA_CM31_mul_weak (R17CurrentCM31Semantics.toArithmetic a)
    (R17CurrentCM31Semantics.toArithmetic b) ha hb hc hd
  refine ⟨R17CurrentCM31Semantics.fromArithmetic z, ?_, h1, h2⟩
  simp only [R17CurrentCM31Semantics.operations, hz, bind_tc_ok]

#print axioms const0
#print axioms const1
#print axioms QA_sub_pres
#print axioms QA_add_pres
#print axioms QA_mul_pres
#print axioms QA_double_pres
#print axioms S7_double_pres
#print axioms S7_t2_pres
#print axioms NBF_BasisInstall_install_W
#print axioms SAQ_Query_install_W
#print axioms LIBC_QueryOps_seed_W
#print axioms NJJ_QueryOps_concrete_W
#print axioms SAQ_Geometry_install_W
#print axioms R17_M31_operations_W
#print axioms R17_CM31_operations_new_W
#print axioms R17_CM31_operations_mul_W
end AspisR1.NPH_R22Installers
