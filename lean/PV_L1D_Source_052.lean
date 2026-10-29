import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_052
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (h1 : alloc.vec.Vec aspis_core.field.QM31)
  (g : Array aspis_core.field.QM31 1024#usize)
  (d : Array aspis_core.field.QM31 1024#usize) :
  Logged (Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let columns ← PV_L1D_Logged.lift (core.default.DefaultArray.default 29#usize
      (alloc.vec.Vec.Insts.CoreDefaultDefault aspis_core.field.QM31))
  let columns1 ← PV_L1D_Logged.lift (host_semantic.lift_columns_loop0 c1 columns 0#usize)
  massert (26#usize < 29#usize)
  let (v, index_mut_back) ← PV_L1D_Logged.lift (Array.index_mut_usize columns1 26#usize)
  let columns2 := index_mut_back v
  let columns3 ← PV_L1D_Logged.lift (Array.update columns2 26#usize h1)
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice g))
  let v1 ← PV_L1D_Logged.lift (alloc.slice.Slice.to_vec aspis_core.field.QM31.Insts.CoreCloneClone s)
  massert (27#usize < 29#usize)
  let (v2, index_mut_back1) ← PV_L1D_Logged.lift (Array.index_mut_usize columns3 27#usize)
  let columns4 := index_mut_back1 v2
  let columns5 ← PV_L1D_Logged.lift (Array.update columns4 27#usize v1)
  let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice d))
  let v3 ← PV_L1D_Logged.lift (alloc.slice.Slice.to_vec aspis_core.field.QM31.Insts.CoreCloneClone s1)
  massert (28#usize < 29#usize)
  let (v4, index_mut_back2) ← PV_L1D_Logged.lift (Array.index_mut_usize columns5 28#usize)
  let columns6 := index_mut_back2 v4
  Array.update columns6 28#usize v3

theorem complete_result
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (h1 : alloc.vec.Vec aspis_core.field.QM31)
  (g : Array aspis_core.field.QM31 1024#usize)
  (d : Array aspis_core.field.QM31 1024#usize) :
  erase (produce c1 h1 g d) = host_semantic.lift_columns c1 h1 g d := by
  unfold produce
  conv_rhs => unfold host_semantic.lift_columns
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_052
