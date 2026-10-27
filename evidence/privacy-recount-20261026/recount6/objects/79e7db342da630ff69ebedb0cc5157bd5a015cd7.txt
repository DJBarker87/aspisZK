import R1Z.ProverRwSuccessErrorSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessErrorInstall
open Aeneas Aeneas.Std Result ProverRwFull
attribute [local instance] Classical.propDecidable
abbrev Src := ProverRwSuccessErrorSource.r1_wire.Error.Insts.CoreCmpPartialEqError.eq
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessHeapInstall.selected ops with op256 := Src}
theorem source (ops : ExternalFuns) (a b : r1_wire.Error) :
    (selected ops).op256 a b = Src a b := rfl
-- Twelve error constructors, with only scalar comparisons in payload branches.
theorem exact (a b : r1_wire.Error) : Src a b=.ok (decide (a=b)) := by
  cases a <;> cases b <;>
    simp [Src,ProverRwSuccessErrorSource.r1_wire.Error.Insts.CoreCmpPartialEqError.eq,
      read_discriminant,r1_wire.Error.read_discriminant,
      core.cmp.impls.PartialEqU8.eq,core.cmp.impls.PartialEqUsize.eq,lift,bind_tc_ok]
  all_goals split <;> simp_all
#print axioms source
#print axioms exact
end R1Z.ProverRwSuccessErrorInstall
