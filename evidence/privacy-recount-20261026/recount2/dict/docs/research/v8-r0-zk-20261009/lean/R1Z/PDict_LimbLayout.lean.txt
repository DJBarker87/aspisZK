import R1Z.PDict_CodecDictionary
set_option autoImplicit false
namespace R1Z.PDict_LimbLayout
open Aeneas Aeneas.Std Result ProverRwFull

theorem limbs (x : aspis_core.field.wide_exact.WideExact) :
    PDict_CodecSource.aspis_core.field.wide_exact.WideExact.to_limbs x =
    .ok (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
      x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) := rfl

theorem selected_layout (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (x : aspis_core.field.wide_exact.WideExact) :
    (PDict_CodecDictionary.selected base ops).op49 x =
    .ok (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
      x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) := by
  rw [PDict_CodecDictionary.op49_installed]
  exact limbs x

#print axioms limbs
#print axioms selected_layout
end R1Z.PDict_LimbLayout
