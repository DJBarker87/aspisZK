import NDD_Reference.Funs
import AspisR1SelectedMaskProbe.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Prepared
open AspisR1SelectedMaskProbe

theorem prepared (x : field.QM31) :
    NDD_Reference.prepared_ref
      (Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]) =
      (do let p ← field.PreparedQm31Multiplier.new x
          ok p.components) := by
  simp [NDD_Reference.prepared_ref,NDD_Reference.add_ref,
    Array.index_usize,Array.make,
    field.PreparedQm31Multiplier.new,
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    field.CM31.add,field.M31.add,field.P]
#print axioms prepared
end NDD_Prepared
