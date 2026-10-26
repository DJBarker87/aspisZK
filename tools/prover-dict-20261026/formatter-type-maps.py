"""Generate structural maps with explicit source and target typeclass arguments."""
from pathlib import Path
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_FormatterTypeMaps.lean'
names={
'Late':('aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1',['live_snapshot','candidate_afterstate']),
'Trace':('aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1',['stable','late','variant','private_directions','value_bits','public_outputs','afterstate']),
'Compilation':('aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1',['trace','semantic_c1','public_statement']),
'CopyLink':('aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1',['id','tag','kind','weight','producer','consumer']),
'Times':('aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes',['public_data','emit','builders','check'])}
mapnames={'Late':'late','Trace':'trace','Compilation':'compilation','CopyLink':'link','Times':'times'}
s='''import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterTypeMaps
open Aeneas Aeneas.Std ProverRwFull
@[reducible] def types (base : ExternalTypes) (F : Type) : ExternalTypes :=
  {base with op27 := F}
'''
for n,(full,fs) in names.items():s+=f'abbrev {n} := @{full}\n'
public='aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public'
s+=f'abbrev Public := @{public}\n'
for n,(full,fs) in names.items():
 for inv in [False,True]:
  fn=('un' if inv else '')+mapnames[n];src='(types base F)' if inv else 'base';dst='base' if inv else '(types base F)'
  args=[]
  for f in fs:
   x=f'(@{full}.{f} {src} x)'
   nested={('Compilation','trace'):'trace',('Compilation','public_statement'):'late'}.get((n,f))
   if nested:x=f'({"un" if inv else ""}{nested} base F {x})'
   args.append(x)
  s+=f'\ndef {fn} (base : ExternalTypes) (F : Type) (x : @{n} {src}) : @{n} {dst} :=\n  @{full}.mk {dst} '+ ' '.join(args)+'\n'
for inv in [False,True]:
 fn='unpublic' if inv else 'pub';src='(types base F)' if inv else 'base';dst='base' if inv else '(types base F)';lm='unlate' if inv else 'late'
 s+=f'\ndef {fn} (base : ExternalTypes) (F : Type) (x : @Public {src}) : @Public {dst} := by\n  cases x with\n'
 for cons in ['Transfer','Withdrawal']:s+=f'  | {cons} p l => exact @{public}.{cons} {dst} p ({lm} base F l)\n'
for n in names:
 fn=mapnames[n]
 s+=f'\ntheorem {fn}_roundtrip (b : ExternalTypes) (F : Type) (x : @{n} b) :\n    un{fn} b F ({fn} b F x) = x := by cases x; rfl\n'
s+='\ntheorem public_roundtrip (b : ExternalTypes) (F : Type) (x : @Public b) :\n    unpublic b F (pub b F x) = x := by cases x <;> rfl\n'
for fn in [*mapnames.values(),'public']:s+=f'\n#print axioms {fn}_roundtrip'
s+='\nend R1Z.PDict_FormatterTypeMaps\n';p.write_text(s)
