"""Private-cohort reuse of original-verdict proofs; no shared source writes.
Only namespaces, carrier aliases and already-proved generic helper names change.
"""
from pathlib import Path
import subprocess,re,json,hashlib,sys
E=Path('evidence/pv-batch1-20261027');O=E/'lean';branch='codex/pv-cb3-20261026'
rev=subprocess.check_output(['git','rev-parse',branch],text=True).strip();base='docs/research/v8-r0-zk-20261009/lean/R1Z/'
known={'PV_CB3_Op258Ref':'PV_B1_PoleOriginal','PV_CB3_Op258Equal':'PV_B1_OriginalEqualTotal','PV_CB3_MaskShift':'PV_B1_MaskShift','PV_CB3_MaskCast':'PV_B1_MaskCast','PV_CB3_LoopEquations':'PV_B1_LoopSteps','PV_CB3_IndexFailure':'PV_B1_ArrayRead','PV_CB3_StagedComposition':'PV_B1_ReadTotal'}
sources={};order=[]
def visit(m):
 if m in known or m in sources:return
 p=base+m+'.lean';s=subprocess.check_output(['git','show',rev+':'+p],text=True)
 assert 'ExternalFuns' not in s and 'ExternalTypes' not in s,(m,'unexpected callback quantifier')
 sources[m]=s
 for dep in re.findall(r'^import R1Z\.(\S+)',s,re.M):visit(dep)
 order.append(m)
for root in ['PV_CB3_Op258FoldAll','PV_CB3_Op258RowLaw']:visit(root)
mapping={**known,**{m:'PV_B1_Orig258_'+m.removeprefix('PV_CB3_') for m in order}}
rows=[]
for m in order:
 old=sources[m];s=old
 # Source equal theorem retains its checked declaration; only the totality
 # supplement lives in the mapped module.
 s=s.replace('PV_CB3_Op258Equal.source','PV_B1_PoleOriginalEqual.source')
 for a,b in sorted(mapping.items(),key=lambda x:-len(x[0])):
  s=s.replace('R1Z.'+a,b).replace(a,b)
 s=s.replace('ProverRwFull','PV_B1_258')
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|\baxiom\s',s),m
 p=O/(mapping[m]+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
 rows.append(dict(module=mapping[m],predecessor_module=m,predecessor_path=base+m+'.lean',predecessor_sha256=hashlib.sha256(old.encode()).hexdigest(),private_source_sha256=hashlib.sha256(s.encode()).hexdigest()))
manifest=dict(predecessor_revision=rev,changes=['private namespace/import renaming','ProverRwFull raw carrier replaced by the identical fresh extracted carrier','generic read/index/loop/mask and equality lemmas redirected to checked private equivalents'],statements='Input bounds and quantifiers retained; no source law is credited from these uncompiled files',rows=rows)
p=E/'original-classification-port.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps([r['module'] for r in rows]),flush=True)
