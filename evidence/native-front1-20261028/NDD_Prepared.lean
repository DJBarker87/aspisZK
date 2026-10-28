import NDD_Reference.Funs
import NDD_ResultLaws
import AspisR1SelectedMaskProbe.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Prepared
open AspisR1SelectedMaskProbe

theorem add_reference (x y : U32) :
    NDD_Reference.add_ref x y = field.M31.add x y := by
  simp [NDD_Reference.add_ref,field.M31.add,field.P]

theorem prepared (x : field.QM31) :
    NDD_Reference.prepared_ref
      (Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]) =
      (do let p ← field.PreparedQm31Multiplier.new x
          ok p.components) := by
  simp [NDD_Reference.prepared_ref,add_reference,
    Array.index_usize,Array.make,
    field.PreparedQm31Multiplier.new,
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    field.CM31.add]
#print axioms add_reference
#print axioms prepared
end NDD_Prepared
