from pathlib import Path
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_PureDictionary.lean'
fields={37:'PDict_PureSource.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq',40:'PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone',41:'PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq',43:'PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c0',44:'PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c1',60:'PDict_PureSource.aspis_core.field.CM31.new',235:'PDict_ConstantsSource.leaf_bits',236:'PDict_ConstantsSource.max_batch',239:'PDict_ConstantsSource.claims',240:'PDict_ConstantsSource.lanes',260:'PDict_ConstantsSource.domain'}
s='''import R1Z.PDict_RejectionStd
import R1Z.PDict_PureSource
import R1Z.PDict_ConstantsSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_PureDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_RejectionStd.native
/-- Six complete core bodies and five constants-inclusive source bodies.
No external template or unknown callback implements these eleven fields. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_RejectionStd.selected base ops with
'''
for i,v in fields.items():s+=f'    op{i} := {v}\n'
s+='  }\n'
for i,v in fields.items():
 s+=f'\ntheorem op{i}_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :\n    (selected base ops).op{i} = {v} := rfl\n#print axioms op{i}_installed\n'
s+='end R1Z.PDict_PureDictionary\n';p.write_text(s)
