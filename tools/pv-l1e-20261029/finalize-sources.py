"""Freeze accepted roots and generate the statement, axioms, and replay audits."""
from pathlib import Path
import json,hashlib,re
E=Path('evidence/pv-l1e-20261029')
accepted={v['module']:v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
roots=[];names=[];sources=[]
for p in sorted(Path('lean').glob('PV_L1E_*.lean')):
 m=p.stem
 if m in ['PV_L1E_Statements','PV_L1E_Axioms','PV_L1E_FocusedReplay']:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert m in accepted and accepted[m]['source_sha256']==sha,('unaccepted current source',m)
 roots.append(m);sources.append(dict(module=m,path=str(p),sha256=sha,revision=accepted[m]['source_revision'],status='checked model or conditional interface; no native instance'))
 for line in accepted[m]['axioms']:
  n=re.match(r"'([^']+)'",line)[1]
  if n not in names:names.append(n)
imports=''.join('import '+m+'\n' for m in roots)
combined='''set_option autoImplicit false
namespace PV_L1E_Statements
open PV_RJ4IDB
open PV_L1E_CountSkeleton PV_L1E_OriginalCountSkeleton
/-- Combined conditional COUNT input and the existing lossless native decoder.
The original four source/world links remain explicit and uninstantiated. -/
theorem combined {I A S P : Type} (actualCount : I → List Nat × List Nat)
    (native : I → NativeTrace A) (sourceWorld bodyWorld : I → Trace A)
    (owner : I → R1Z.SideChannelL1AttemptRecord.Owner S P)
    (initial : I → S) (fuel index : I → Nat)
    (adapt : I → R1Z.SideChannelL1AttemptRecord.Run P × S → Trace A)
    (acquisition : PV_L1E_Link_CountAcquisition actualCount sourceWorld)
    (body : PV_L1E_Link_BodyWrapper sourceWorld bodyWorld)
    (retry : PV_L1E_Link_OriginalRetry bodyWorld owner initial fuel index adapt)
    (coupling : PV_L1E_Link_NativeD163 native owner initial fuel index adapt) :
    PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native ∧
      ∀ i, nativeObservation (native i) = decoder (modelTrace (native i)) :=
  ⟨original_count_trace actualCount native sourceWorld bodyWorld owner initial fuel index adapt
      acquisition body retry coupling,PV_RJ4IDB.all_prefixes native⟩
#print combined
#print axioms combined
end PV_L1E_Statements
'''
links=['PV_L1E_CountSkeleton.'+x for x in ['PV_L1E_Link_CountAcquisition','PV_L1E_Link_BodyWrapper','PV_L1E_Link_RetryJoin','PV_L1E_Link_NativeOriginal']]
links+=['PV_L1E_OriginalCountSkeleton.'+x for x in ['PV_L1E_Link_OriginalRetry','PV_L1E_Link_NativeD163']]
links+=['PV_L1E_OwnerJoin.PV_L1E_Link_SourceOwner']
links+=['PV_L1E_SourceOwnerLinks.'+x for x in ['PV_L1E_Link_OwnerControl','PV_L1E_Link_OwnerEvents']]
Path('lean/PV_L1E_Statements.lean').write_text(imports+combined+''.join('#check '+n+'\n' for n in names)+''.join('#print '+n+'\n' for n in links)+''.join('#check PV_RJ4IDB.OpenInputs.'+n+'\n' for n in ['L1_COUNT_TRACE','L1_ORACLE_PREFIX','L1_TIME_TRACE','L1_RETAINED_SIDECHANNELS']))
reused=['R1Z.ProverRwRetryModel.retry','R1Z.SideChannelL1AttemptRecord.erase_run','R1Z.SideChannelEntropyLaw.first_accepted','R1Z.SideChannelEntropyLaw.sixteen_exhaustion','R1Z.SideChannelRetryLaw.actual_entry_mass','PV_DIAG2.source_client_no_rejected','PV_RJ4IDB.native_factorization']
Path('lean/PV_L1E_Axioms.lean').write_text('import PV_L1E_Statements\nimport R1Z.SideChannelEntropyLaw\n'+''.join('#print axioms '+n+'\n' for n in names+reused+['PV_L1E_Statements.combined']))
Path('lean/PV_L1E_FocusedReplay.lean').write_text('''import PV_L1E_Axioms
/-! One focused replay of the accepted source-count closure, not a deployed
privacy release or construction of any OPEN native input. -/
#print axioms PV_L1E_Statements.combined
#print axioms PV_L1E_OriginalSourceCount.same_original_success
#print axioms PV_L1E_RetrySource.complete_source
''')
(E/'final-source-manifest.json').write_text(json.dumps(dict(roots=roots,theorems=names,sources=sources,drafts=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),status='unattempted, zero theorem credit') for p in E.glob('drafts-*.lean.txt')]),indent=2)+'\n')
print('Accepted roots',len(roots),'printed theorem names',len(names))
