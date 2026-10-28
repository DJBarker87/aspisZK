import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BasisEquation38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem step [ExternalFuns]
  (basis : Array aspis_core.field.M31 28#usize)
  (denominator : aspis_core.field.M31) (degree : Std.Usize) (i : Std.Usize)
  (j : Std.Usize) :
  host_sumcheck.interpolation_basis_steps basis denominator degree i j =
  (do
  if j = 28#usize
  then ok (basis, denominator)
  else
    if i = j
    then
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add j 1#usize)
      host_sumcheck.interpolation_basis_steps basis denominator degree i i1
    else
      let basis1 ← host_sumcheck.interpolation_extend basis degree j
      let i1 ← Aeneas.Std.lift (UScalar.cast .U32 i)
      let i2 ← Aeneas.Std.lift (UScalar.cast .U32 j)
      let m ← aspis_core.field.M31.sub i1 i2
      let denominator1 ← aspis_core.field.M31.mul denominator m
      let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_add degree 1#usize)
      let i4 ← Aeneas.Std.lift (Std.Usize.wrapping_add j 1#usize)
      host_sumcheck.interpolation_basis_steps basis1 denominator1 i3 i i4) := by
  rw [host_sumcheck.interpolation_basis_steps]

#print axioms step
end R1Z.PV_RunJoin_BasisEquation38
