import LPi_TowerValues
import XRy_ClaimArithmetic
set_option autoImplicit false
namespace AspisR1.LPq_ScalarPorts
open Aeneas Aeneas.Std Result

theorem add (x y : U32) : FIo_Native.aspis_core.field.M31.add x y=
    XRn_Join_Field.field.M31.add x y := by
  simp only [FIo_Native.aspis_core.field.M31.add,XRn_Join_Field.field.M31.add,
    FIo_Native.aspis_core.field.P,XRn_Join_Field.field.P]

theorem sub (x y : U32) : FIo_Native.aspis_core.field.M31.sub x y=
    XRn_Join_Field.field.M31.sub x y := by
  simp only [FIo_Native.aspis_core.field.M31.sub,XRn_Join_Field.field.M31.sub,
    FIo_Native.aspis_core.field.P,XRn_Join_Field.field.P]

theorem reduce (x : U64) : FIo_Native.aspis_core.field.reduce_u64 x=
    XRn_Join_Field.field.reduce_u64 x := by
  simp only [FIo_Native.aspis_core.field.reduce_u64,XRn_Join_Field.field.reduce_u64,
    FIo_Native.aspis_core.field.P,XRn_Join_Field.field.P]

theorem wrapper (x : U64) : FIo_Native.aspis_core.field.M31.reduce_u64 x=
    XRn_Join_Field.field.M31.reduce_u64 x := by
  simp only [FIo_Native.aspis_core.field.M31.reduce_u64,XRn_Join_Field.field.M31.reduce_u64,reduce]

theorem mul (x y : U32) : FIo_Native.aspis_core.field.M31.mul x y=
    XRn_Join_Field.field.M31.mul x y := by
  simp only [FIo_Native.aspis_core.field.M31.mul,XRn_Join_Field.field.M31.mul,reduce]

theorem double (x : U32) : FIo_Native.aspis_core.field.M31.double x=
    XRn_Join_Field.field.M31.double x := by
  simp only [FIo_Native.aspis_core.field.M31.double,XRn_Join_Field.field.M31.double,add]

#print axioms add
#print axioms sub
#print axioms reduce
#print axioms wrapper
#print axioms mul
#print axioms double
end AspisR1.LPq_ScalarPorts
