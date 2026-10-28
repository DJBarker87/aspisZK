"""One final combined public audit, then a distinct focused five-row replay."""
from pathlib import Path
import json,hashlib,re
E=Path('evidence/pv-batch2-20261027/batch2f');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
base=json.loads((E.parent/'batch2e/AUDIT-PREFLIGHT.json').read_text());decls=list(base['public_declarations']);accepted=json.loads((E/'ACCEPTED-PROGRESS.json').read_text())['sources']
for a in accepted:
 p=Path(a['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==a['source_sha256'],a['module']
 for d in a['declarations']:
  n=d['declaration']
  if n.startswith('_private') or '._private' in n:continue
  if n not in decls:decls.append(n)
s='import R1Z.PV_B2_F_FiveRows\nimport R1Z.PV_B2_F_BoxCounterexample\n\n-- Complete current public source/predecessor audit; failed recovery objects excluded.\n'+'\n'.join('#print axioms '+n for n in decls)+'\n'
p=L/'PV_B2_F_AuditCombined.lean';p.write_text(s)
old=(L/'PV_B2_F_FiveRows.lean').read_text();replay='''import R1Z.PV_B2_F_AuditCombined
import R1Z.PV_B2_F_FiveRows
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_AuditClosure
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier PV_B2_F_RawNative
abbrev E := ProverRwFull.aspis_core.field.wide_exact.WideExact
'''
for name,new,args in [('five_rows','closed_rows','base heap box ops b w kappa v alpha z kind j'),('nonvacuity','nonvacuity','base ops b kappa v alpha z')]:
 start=old.index('theorem '+name+' ');end=old.index(' := by',start);head=old[start:end].replace('theorem '+name+' ','theorem '+new+' ',1)
 replay+='\n'+head+' :=\n  PV_B2_F_FiveRows.'+name+' '+args+'\n'
queries=['closed_rows','nonvacuity','PV_B2_E_GammaOriginal.copy_equal_original','PV_B2_E_GammaOriginal.gamma_law','PV_B2_E_GammaOriginal.nonvacuity','PV_B2_E_OrdinaryOriginal.copy_equal_original','PV_B2_E_Install250.value_law','PV_B2_E_Install250.nonvacuity','PV_B2_F_MaterializeRequest.complete_result','PV_B2_F_ResourceFamilies.heap_source','PV_B2_F_ResourceFamilies.box_source','PV_B2_F_ConstructorEffect.value_law','PV_B2_F_ConstructorCarrierLaws.weight_roundtrip','PV_B2_F_RawNative.copy_equal_original','PV_B2_F_RawNative.valid_value_law','PV_B2_F_RawNative.dictionaries','PV_B2_F_RawNative.observations','PV_B2_F_RawNative.preserved_254']
replay+='\n'+'\n'.join('#print axioms '+n for n in queries)+'\nend PV_B2_F_AuditClosure\n';(L/'PV_B2_F_AuditClosure.lean').write_text(replay)
(E/'FINAL-AUDIT-PLAN.json').write_text(json.dumps(dict(audit_target='R1Z/PV_B2_F_AuditCombined',audit_id=40897,replay_target='R1Z/PV_B2_F_AuditClosure',replay_id=40898,reserved_fallback=40899,public_queries=len(decls),public_declarations=decls,current_accepted_sources=accepted,rows=['V256','V257','V258','V259','V260'],existing_credit='V261 shared op254 counted once; preserved_254 queried',ordering='after current ordered fixture-byte gate',source_scope='selected source/callback cohort; no complete privacy endpoint or physical-observation replay'),indent=2)+'\n')
print('prepared',len(decls),'public audits, then focused five-row replay')
