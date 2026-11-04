import Lean
import NFN_PhaseTransport
import NFS_NEI_FieldCarriers

set_option autoImplicit false
noncomputable section
namespace NFS_NEI_FieldScalar
open Aeneas Aeneas.Std Result

theorem m_add (x y : U32) :
    NEI_LineFull.aspis_core.field.M31.add x y = AspisR1CurrentWide.field.M31.add x y := by
  simp only [NEI_LineFull.aspis_core.field.M31.add, AspisR1CurrentWide.field.M31.add,
    NEI_LineFull.aspis_core.field.P, AspisR1CurrentWide.field.P]

theorem m_sub (x y : U32) :
    NEI_LineFull.aspis_core.field.M31.sub x y = AspisR1CurrentWide.field.M31.sub x y := by
  simp only [NEI_LineFull.aspis_core.field.M31.sub, AspisR1CurrentWide.field.M31.sub,
    NEI_LineFull.aspis_core.field.P, AspisR1CurrentWide.field.P]

theorem reduce (x : U64) : NEI_LineFull.aspis_core.field.reduce_u64 x =
    AspisR1CurrentWide.field.reduce_u64 x := by
  simp only [NEI_LineFull.aspis_core.field.reduce_u64, AspisR1CurrentWide.field.reduce_u64,
    NEI_LineFull.aspis_core.field.P, AspisR1CurrentWide.field.P]

theorem m_reduce_u64 (x : U64) : NEI_LineFull.aspis_core.field.M31.reduce_u64 x =
    AspisR1CurrentWide.field.M31.reduce_u64 x := by
  simp only [NEI_LineFull.aspis_core.field.M31.reduce_u64,
    AspisR1CurrentWide.field.M31.reduce_u64, reduce]

theorem m_mul (x y : U32) : NEI_LineFull.aspis_core.field.M31.mul x y =
    AspisR1CurrentWide.field.M31.mul x y := by
  simp only [NEI_LineFull.aspis_core.field.M31.mul, AspisR1CurrentWide.field.M31.mul,reduce]

theorem m_double (x : U32) : NEI_LineFull.aspis_core.field.M31.double x =
    AspisR1CurrentWide.field.M31.double x := by
  simp only [NEI_LineFull.aspis_core.field.M31.double, AspisR1CurrentWide.field.M31.double,m_add]

#print axioms m_add
#print axioms m_sub
#print axioms reduce
#print axioms m_reduce_u64
#print axioms m_mul
#print axioms m_double
end NFS_NEI_FieldScalar
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
