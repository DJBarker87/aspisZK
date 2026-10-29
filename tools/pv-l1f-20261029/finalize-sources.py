"""Freeze the accepted proof roots and emit one statement/audit/focused replay."""
from pathlib import Path
import json,hashlib,re
E=Path('evidence/pv-l1f-20261029')
accepted={v['module']:v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
roots=[];names=[];sources=[];drafts=[]
for p in sorted(Path('lean').glob('PV_L1F_*.lean')):
 m=p.stem
 if m in ['PV_L1F_Statements','PV_L1F_Axioms','PV_L1F_FocusedReplay']:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if m not in accepted or accepted[m]['source_sha256']!=sha:
  dst=E/('draft-'+p.name+'.txt');dst.write_bytes(p.read_bytes());p.unlink();drafts.append(dict(path=str(dst),sha256=sha,status='unaccepted draft, zero theorem credit'));continue
 roots.append(m);sources.append(dict(module=m,path=str(p),sha256=sha,revision=accepted[m]['source_revision'],status='checked local source/model or conditional interface; no full native instance'))
 for line in accepted[m]['axioms']:
  n=re.match(r"'([^']+)'",line)[1]
  if n not in names:names.append(n)
imports=''.join('import '+m+'\n' for m in roots)+'import PV_L1E_OriginalCountSkeleton\nimport PV_DIAG10_Operands\n'
combined='''set_option autoImplicit false
namespace PV_L1F_Statements
open PV_RJ4IDB PV_L1E_CountSkeleton PV_L1E_OriginalCountSkeleton
/-- Conditional composition only: all four frozen trace links and the frozen
joint diagnostic site law remain explicit. No concrete native instance or
original-to-simE coupling is manufactured by this conjunction. -/
theorem combined {I A S P C : Type} (actualCount : I → List Nat × List Nat)
 (native : I → NativeTrace A) (sourceWorld bodyWorld : I → Trace A)
 (owner : I → R1Z.SideChannelL1AttemptRecord.Owner S P)
 (initial : I → S) (fuel index : I → Nat)
 (adapt : I → R1Z.SideChannelL1AttemptRecord.Run P × S → Trace A)
 (context : I → C) (calls : I → PV_DIAG9.DiagnosticCall)
 (acquisition : PV_L1E_Link_CountAcquisition actualCount sourceWorld)
 (body : PV_L1E_Link_BodyWrapper sourceWorld bodyWorld)
 (retry : PV_L1E_Link_OriginalRetry bodyWorld owner initial fuel index adapt)
 (coupling : PV_L1E_Link_NativeD163 native owner initial fuel index adapt)
 (sites : PV_DIAG10.PV_DIAG10_Link_Sites context calls) :
 OpenInputs.L1_COUNT_TRACE actualCount native ∧
 PV_DIAG10.PV_DIAG10_Link_Sites context calls ∧
 ∀ i, nativeObservation (native i)=decoder (modelTrace (native i)) :=
 ⟨original_count_trace actualCount native sourceWorld bodyWorld owner initial fuel index adapt
   acquisition body retry coupling,sites,PV_RJ4IDB.all_prefixes native⟩
#print combined
#print axioms combined
end PV_L1F_Statements
'''
Path('lean/PV_L1F_Statements.lean').write_text(imports+combined)
links=['PV_L1E_CountSkeleton.PV_L1E_Link_CountAcquisition','PV_L1E_CountSkeleton.PV_L1E_Link_BodyWrapper','PV_L1E_OriginalCountSkeleton.PV_L1E_Link_OriginalRetry','PV_L1E_OriginalCountSkeleton.PV_L1E_Link_NativeD163','PV_DIAG10.PV_DIAG10_Link_Sites']
Path('lean/PV_L1F_Axioms.lean').write_text('import PV_L1F_Statements\n'+''.join('#print axioms '+n+'\n' for n in names+['PV_L1F_Statements.combined'])+''.join('#print '+n+'\n' for n in links))
Path('lean/PV_L1F_FocusedReplay.lean').write_text('import PV_L1F_Axioms\n/-- Focused accepted closure only; no deployed privacy release claim. -/\n#check PV_L1F_Statements.combined\n'+''.join('#check '+n+'\n' for n in names)+'#print axioms PV_L1F_Statements.combined\n')
(E/'final-source-manifest.json').write_text(json.dumps(dict(roots=roots,theorems=names,sources=sources,drafts=drafts),indent=2))
print('Accepted roots',len(roots),'theorems',len(names),'drafts',len(drafts))
