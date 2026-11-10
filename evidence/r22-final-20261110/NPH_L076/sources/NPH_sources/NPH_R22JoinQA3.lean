import NPH_R22Join094
import NOC_Run5bHost
import NNH_CorrectConfiguration
import Port5Q1_GeometryTerminal

/-! NPH_ (R22, QA contexts): the installer contexts outside 094 and the NFN op14/op15 contexts.
Every executing QA call of the query and geometry bodies receives W arguments for EVERY input
of the body. The textual screen of the bodies (Port3_NativeQueryBody, Port3_NativeGeometryBody)
gives the call patterns:
- query: `op7 z z; op8; op6 · one` (query_values and accumulate_batched_with_node_loop0.body,
  where `one` is the op5 output passed unchanged through the loop), and `op7 m node`
  (M31.mul, TOTAL);
- geometry (for_range_loop0.body): `op9 x x; op10; op7; op8` on the op14 output, op14/op15 on a
  fibre index, op9 in the suffix loop (M31.mul, TOTAL).
`query_sites` and `geometry_triple` are generic over any record with the installed slots;
`geometry_line`/`geometry_point` give, for every fibre index, either ok W or an out-of-bounds
TABLE_B read (bounds-checked in both profiles, no QA call executed). `nea_line_W` does the same
for the NFN_NEB_GeometryPrimitives op14 (line_node over NFN_NEA_FieldProduct.ops, whose fibre
point is a FIo_Native CM31 product of canonical table entries). The slot identifications are rfl:
the deployed geometry is NFN_NEW_GeometryDictionary.adopted in both host configurations
(`cfg_geometry`, `host_geometry`), executed as Port5Q1_GeometryTerminal.install adopted
(Tx1Q_Execution geometry_call). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinQA3
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Installers

abbrev QAmul := AspisR1Qm31ArithmeticProbe.field.M31.mul
abbrev QAsub := AspisR1Qm31ArithmeticProbe.field.M31.sub
abbrev QAdouble := AspisR1Qm31ArithmeticProbe.field.M31.double

theorem mul_lt (z w : U32) : ∃ m, QAmul z w = ok m ∧ W m := by
  obtain ⟨m, hm, vm⟩ := AspisR1.NPH_R22FieldRef.refMul_total z w
  refine ⟨m, ?_, Nat.le_of_lt vm⟩
  show AspisR1Qm31ArithmeticProbe.field.M31.mul z w = ok m
  rw [AspisR1.NPH_R22FieldCopies.QA_M31_mul_eq]; exact hm
#print axioms mul_lt

/-! ### query bodies -/

/-- The node pattern of query_values and accumulate_batched_with_node_loop0.body, for every z
and every W `one`: op8 receives a W product and op6 receives W arguments. -/
theorem query_sites (O : Port3_NativeQueryBody.Ops) (h7 : O.op7 = QAmul) (h6 : Pres2 O.op6)
    (h8 : Pres1 O.op8) (z one : U32) (hone : W one) :
    ∃ m m1 node, O.op7 z z = ok m ∧ W m ∧ O.op8 m = ok m1 ∧ W m1 ∧
      O.op6 m1 one = ok node ∧ W node := by
  obtain ⟨m, hm, wm⟩ := mul_lt z z
  obtain ⟨m1, h1, w1⟩ := h8 m wm
  obtain ⟨node, h2, w2⟩ := h6 m1 one w1 hone
  exact ⟨m, m1, node, by rw [h7]; exact hm, wm, h1, w1, h2, w2⟩
#print axioms query_sites

theorem Dcon_sites (z : U32) :
    ∃ one, NPH_R22Join094.Dcon.op5 = ok one ∧ W one ∧ ∃ m m1 node, NPH_R22Join094.Dcon.op7 z z = ok m ∧
      W m ∧ NPH_R22Join094.Dcon.op8 m = ok m1 ∧ W m1 ∧ NPH_R22Join094.Dcon.op6 m1 one = ok node ∧ W node := by
  obtain ⟨h5, h6, h7, h8⟩ := NPH_R22Join094.Dcon_scalar
  refine ⟨1#u32, h5, by unfold W; first | decide | simp, ?_⟩
  exact query_sites _ h7 (by rw [h6]; exact QA_sub_pres) (by rw [h8]; exact fun x hx => QA_add_pres x x hx hx)
    z 1#u32 (by unfold W; first | decide | simp)
#print axioms Dcon_sites

theorem Dsel_sites (z : U32) :
    ∃ one, NPH_R22Join094.Dsel.op5 = ok one ∧ W one ∧ ∃ m m1 node, NPH_R22Join094.Dsel.op7 z z = ok m ∧
      W m ∧ NPH_R22Join094.Dsel.op8 m = ok m1 ∧ W m1 ∧ NPH_R22Join094.Dsel.op6 m1 one = ok node ∧ W node := by
  obtain ⟨h5, h6, h7, h8⟩ := NPH_R22Join094.Dsel_scalar
  refine ⟨1#u32, h5, by unfold W; first | decide | simp, ?_⟩
  exact query_sites _ h7 (by rw [h6]; exact QA_sub_pres) (by rw [h8]; exact fun x hx => QA_add_pres x x hx hx)
    z 1#u32 (by unfold W; first | decide | simp)
#print axioms Dsel_sites

theorem NBF_op7 (o : Port3_NativeQueryBody.Ops) : (NBF_BasisInstall.install o).op7 = QAmul := rfl
#print axioms NBF_op7

/-- Any NBF-installed dictionary (the op4-op8 installer of NFS_QueryOps.installed). -/
theorem NBF_sites (o : Port3_NativeQueryBody.Ops) (z one : U32) (hone : W one) :
    ∃ m m1 node, (NBF_BasisInstall.install o).op7 z z = ok m ∧ W m ∧
      (NBF_BasisInstall.install o).op8 m = ok m1 ∧ W m1 ∧
      (NBF_BasisInstall.install o).op6 m1 one = ok node ∧ W node :=
  query_sites _ (NBF_op7 o) (NBF_BasisInstall_install_W o).op6 (NBF_BasisInstall_install_W o).op8 z one hone
#print axioms NBF_sites

/-- S7Kani3BasisOuter.t2 (basis_levels_owned and levels): the same node pattern, every input. -/
theorem t2_sites (x : U32) :
    ∃ m d z, QAmul x x = ok m ∧ W m ∧ S7Kani3BasisOuter.double m = ok d ∧ W d ∧
      QAsub d 1#u32 = ok z ∧ W z := by
  obtain ⟨m, hm, wm⟩ := mul_lt x x
  obtain ⟨d, hd, wd⟩ := S7_double_pres m wm
  obtain ⟨z, hz, wz⟩ := QA_sub_pres d 1#u32 wd (by unfold W; first | decide | simp)
  exact ⟨m, d, z, hm, wm, hd, wd, hz, wz⟩
#print axioms t2_sites

/-! ### geometry body -/

/-- The three-call pattern of for_range_loop0.body, for every x. -/
theorem geometry_triple {C : Type} (G : Port3_NativeGeometryBody.Ops C) (h7 : G.op7 = ok 1#u32)
    (h8 : G.op8 = QAsub) (h9 : G.op9 = QAmul) (h10 : G.op10 = QAdouble) (x : U32) :
    ∃ m d z, G.op9 x x = ok m ∧ W m ∧ G.op10 m = ok d ∧ W d ∧ G.op7 = ok 1#u32 ∧
      G.op8 d 1#u32 = ok z ∧ W z := by
  obtain ⟨m, hm, wm⟩ := mul_lt x x
  obtain ⟨d, hd, wd⟩ := QA_double_pres m wm
  obtain ⟨z, hz, wz⟩ := QA_sub_pres d 1#u32 wd (by unfold W; first | decide | simp)
  exact ⟨m, d, z, by rw [h9]; exact hm, wm, by rw [h10]; exact hd, wd, h7, by rw [h8]; exact hz, wz⟩
#print axioms geometry_triple

theorem geometry_line {C : Type} (G : Port3_NativeGeometryBody.Ops C) (h14 : G.op14 = SAQ_Geometry.line)
    (u : Usize) :
    (∃ x, G.op14 u = ok x ∧ W x) ∨ (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  rw [h14]; exact NPH_R22Callbacks2.SAQ_Geometry_line_W u
#print axioms geometry_line

theorem geometry_point {C : Type} (G : Port3_NativeGeometryBody.Ops C) (h15 : G.op15 = SAQ_Geometry.point)
    (u : Usize) :
    (∃ p, G.op15 u = ok p ∧ W p.x ∧ W p.y) ∨ (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  rw [h15]; exact NPH_R22Callbacks2.SAQ_Geometry_point_W u
#print axioms geometry_point

/-! ### slot identifications (rfl) -/

theorem adopted_slots :
    NFN_NEW_GeometryDictionary.adopted.op7 = ok 1#u32 ∧ NFN_NEW_GeometryDictionary.adopted.op8 = QAsub ∧
    NFN_NEW_GeometryDictionary.adopted.op9 = QAmul ∧ NFN_NEW_GeometryDictionary.adopted.op10 = QAdouble ∧
    NFN_NEW_GeometryDictionary.adopted.op14 = SAQ_Geometry.line ∧
    NFN_NEW_GeometryDictionary.adopted.op15 = SAQ_Geometry.point :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms adopted_slots

theorem terminal_slots {C : Type} (G : Port3_NativeGeometryBody.Ops C) :
    (Port5Q1_GeometryTerminal.install G).op7 = G.op7 ∧ (Port5Q1_GeometryTerminal.install G).op8 = G.op8 ∧
    (Port5Q1_GeometryTerminal.install G).op9 = G.op9 ∧ (Port5Q1_GeometryTerminal.install G).op10 = G.op10 ∧
    (Port5Q1_GeometryTerminal.install G).op14 = G.op14 ∧ (Port5Q1_GeometryTerminal.install G).op15 = G.op15 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms terminal_slots

theorem fip_geometry {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) : (FIp_Install.configuration err c r).geometry = c.geometry := rfl
#print axioms fip_geometry

theorem deployed_geometry {C : Type} (m : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation) :
    (IDa_Deployed.deployedConfiguration m err r).geometry = m.geometry := rfl
#print axioms deployed_geometry

theorem select_geometry {C : Type} (m : IDa_Deployed.Uninstalled C) (env : RSL.Env) :
    (NNH_Tx2Configuration.select m env).geometry = m.geometry := rfl
#print axioms select_geometry

theorem residual_geometry (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env) :
    (NNH_CorrectConfiguration.residual m env).geometry = NFN_NEW_GeometryDictionary.adopted := by
  unfold NNH_CorrectConfiguration.residual NNH_Tx2SourceConfiguration.fill
  rfl
#print axioms residual_geometry

/-- The geometry of the configuration S c runs (NNH_CorrectConfiguration, any seed). -/
theorem cfg_geometry (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    (NNH_CorrectConfiguration.configuration m env err r).geometry = NFN_NEW_GeometryDictionary.adopted := by
  unfold NNH_CorrectConfiguration.configuration NNH_Tx2Configuration.configuration
  rw [fip_geometry, deployed_geometry, select_geometry, residual_geometry]
#print axioms cfg_geometry

/-- The geometry of the host-context configuration (NOC_Op9Slot, SM5). -/
theorem host_geometry {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).geometry = NFN_NEW_GeometryDictionary.adopted := by
  show (FIp_Install.configuration c.fixed.indexError (NNH_HostCtx.base c) c.fixed.reservation).geometry = _
  rw [fip_geometry]
  show (IDa_Deployed.deployedConfiguration (NNH_HostCtx.missing c) c.fixed.indexError c.fixed.reservation).geometry = _
  rw [deployed_geometry]
  show (NNH_HostCtx.missingLit c).geometry = _
  rw [← NNH_Run5bCtx.missing_at_slot c, select_geometry, residual_geometry]
#print axioms host_geometry

/-- The executed geometry record: every QA call it runs gets W arguments, for every input. -/
theorem deployed_geometry_sites (x : U32) (u : Usize) :
    (∃ m d z, (Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted).op9 x x = ok m ∧ W m ∧
      (Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted).op10 m = ok d ∧ W d ∧
      (Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted).op7 = ok 1#u32 ∧
      (Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted).op8 d 1#u32 = ok z ∧ W z) ∧
    ((∃ x, (Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted).op14 u = ok x ∧ W x) ∨
      (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val)) ∧
    ((∃ p, (Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted).op15 u = ok p ∧ W p.x ∧ W p.y) ∨
      (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val)) := by
  obtain ⟨a7, a8, a9, a10, a14, a15⟩ := adopted_slots
  obtain ⟨t7, t8, t9, t10, t14, t15⟩ := terminal_slots NFN_NEW_GeometryDictionary.adopted
  exact ⟨geometry_triple _ (t7.trans a7) (t8.trans a8) (t9.trans a9) (t10.trans a10) x,
    geometry_line _ (t14.trans a14) u, geometry_point _ (t15.trans a15) u⟩
#print axioms deployed_geometry_sites

theorem SAQ_install_sites {C : Type} (o : Port3_NativeGeometryBody.Ops C) (x : U32) :
    ∃ m d z, (SAQ_Geometry.install o).op9 x x = ok m ∧ W m ∧ (SAQ_Geometry.install o).op10 m = ok d ∧ W d ∧
      (SAQ_Geometry.install o).op7 = ok 1#u32 ∧ (SAQ_Geometry.install o).op8 d 1#u32 = ok z ∧ W z :=
  geometry_triple _ rfl rfl rfl rfl x
#print axioms SAQ_install_sites

theorem NFN_install_sites {C : Type} (o : Port3_NativeGeometryBody.Ops C) (x : U32) :
    ∃ m d z, (NFN_NEB_GeometryPrimitives.install o).op9 x x = ok m ∧ W m ∧
      (NFN_NEB_GeometryPrimitives.install o).op10 m = ok d ∧ W d ∧
      (NFN_NEB_GeometryPrimitives.install o).op7 = ok 1#u32 ∧
      (NFN_NEB_GeometryPrimitives.install o).op8 d 1#u32 = ok z ∧ W z :=
  geometry_triple _ rfl rfl rfl rfl x
#print axioms NFN_install_sites

/-! ### NFN op14/op15 under NFN_NEA_FieldProduct.ops -/

theorem nea_table (q : U32 × U32) :
    AspisR1QueryGeometryActual.fast_domain.table_value NFN_NEA_FieldProduct.ops q = ok ⟨q.1, q.2⟩ := by
  cases q; rfl
#print axioms nea_table

/-- fibre_point under NFN_NEA_FieldProduct.ops (no QA call; FIo_Native CM31.mul of canonical
table entries): ok with canonical coordinates, or an out-of-bounds TABLE_B read. -/
theorem nea_fibre_point_W (u : Usize) :
    (∃ p, AspisR1QueryGeometryActual.fast_domain.fibre_point NFN_NEA_FieldProduct.ops u = ok p ∧
        W p.x ∧ W p.y) ∨
    (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  obtain ⟨i1, hs⟩ := AspisR1.NPH_R22QRawShift.fibre_shift_ok u
  by_cases hb : i1.val < 512
  · left
    have hi := NPH_R22Callbacks2.and511_lt u
    have hA := R17ActualTableArrayIndexV1.tableA_index_entries (u &&& 511#usize) hi
    have cA := NEA_TableCanonical.readA (u &&& 511#usize) hi _ hA
    have hB := R17ActualTableArrayIndexV1.tableB_index_entries i1 hb
    have cB := NEA_TableCanonical.readB i1 hb _ hB
    obtain ⟨z, hz, cz, -⟩ := NFN_NEA_FieldProduct.geometric_cm ⟨_, _⟩ ⟨_, _⟩ cA cB
    refine ⟨{ x := z.a, y := z.b }, ?_, Nat.le_of_lt cz.1, Nat.le_of_lt cz.2⟩
    simp only [AspisR1QueryGeometryActual.fast_domain.fibre_point, AspisR1QueryGeometryActual.domain.FibreIndex.get,
      lift, bind_tc_ok, hA, hs, hB, nea_table, hz]
  · exact Or.inr ⟨i1, hs, by omega⟩
#print axioms nea_fibre_point_W

/-- op14 of NFN_NEB_GeometryPrimitives.install: the R17 M31 mul/double/sub calls receive W
arguments, or the TABLE_B read is out of bounds. -/
theorem nea_line_W (u : Usize) :
    (∃ x, R17FibrePointLineNodeActual.line_node NFN_NEA_FieldProduct.ops R17CurrentM31Semantics.operations u = ok x ∧
        W x) ∨
    (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  rcases nea_fibre_point_W u with ⟨p, hp, wx, _⟩ | h
  · obtain ⟨hmul, hdbl, hsub⟩ := R17_M31_operations_W
    obtain ⟨sq, hsq, wsq⟩ := hmul p.x p.x wx wx
    obtain ⟨m, hm, wm⟩ := hdbl sq wsq
    obtain ⟨z, hz, wz⟩ := hsub m 1#u32 wm (by unfold W; first | decide | simp | scalar_tac)
    exact Or.inl ⟨z, by simp only [R17FibrePointLineNodeActual.line_node, hp, hsq, hm, hz, bind_tc_ok], wz⟩
  · exact Or.inr h
#print axioms nea_line_W

theorem NFN_install_line {C : Type} (o : Port3_NativeGeometryBody.Ops C) (u : Usize) :
    (∃ x, (NFN_NEB_GeometryPrimitives.install o).op14 u = ok x ∧ W x) ∨
    (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) :=
  nea_line_W u
#print axioms NFN_install_line

end AspisR1.NPH_R22JoinQA3
