import NNU_GeometryCallbacks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryInstall
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody
abbrev terminal {C : Type} (g : Ops C) := Port5Q1_GeometryTerminal.install g

theorem gather {C C' : Type} (g : Ops C) (h : Ops C') :
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (terminal g) =
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (terminal h) :=
 NNU_GeometryCallbacks.gather _ _ (by rfl)

theorem zero {C C' : Type} (g : Ops C) (h : Ops C') :
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (terminal g) =
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (terminal h) :=
 NNU_GeometryCallbacks.zero _ _ (by rfl) (by rfl)

theorem prefixCall {C C' : Type} (g : Ops C) (h : Ops C')
 (mul : g.op9=h.op9) (one : g.op7=h.op7) (flat : Slice U32) :
 (terminal g).op13 flat = (terminal h).op13 flat := by
 change Port4C_GeometryInverse.prefixCall g flat=Port4C_GeometryInverse.prefixCall h flat
 simp only [Port4C_GeometryInverse.prefixCall,Port4C_GeometryInverse.leaves,mul,one]

theorem constructor_prefix {C C' : Type} (err : C) (g : Ops C) (h : Ops C')
 (mul : h.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
 (one : h.op7=.ok 1#u32) (flat : Slice U32) :
 (terminal (SAQ_Constructor.install err g)).op13 flat = (terminal h).op13 flat :=
 prefixCall _ _ ((SAQ_Constructor.multiply err g).trans mul.symm)
  ((SAQ_Constructor.one err g).trans one.symm) flat
#print axioms gather
#print axioms zero
#print axioms prefixCall
#print axioms constructor_prefix
end AspisR1.NNU_GeometryInstall
end
