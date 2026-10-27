"""Compile-free import/source provenance. Never calls Lean or changes a host tree."""
from pathlib import Path
import subprocess,hashlib,json,re
root=Path(__file__).resolve().parents[2]
lean=root/'docs/research/v8-r0-zk-20261009/lean'
branches={p:subprocess.check_output(['git','rev-parse',b],cwd=root,text=True).strip() for p,b in {
'ProverRw19':'codex/cx-prover-rw-20261023','ProverRw18ContextDataIff':'codex/cx-prover-rw-20261023',
'PDict_':'codex/cx-prover-dict-20261026','PV_RunJoin_':'codex/pv-runjoin-20261026',
'PV_Src_':'codex/pv-srcid3-20261026'}.items()}
entries={};missing=[]
def get(module):
 rel=module.replace('.','/')+'.lean';path=lean/rel
 if path.is_file():return path.read_bytes(),dict(path=str(path.relative_to(root)),revision='worktree')
 if module.startswith('R1Z.ProverRwFull'):
  path=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(module.split('.')[-1]+'.lean')
  if path.is_file():return path.read_bytes(),dict(path=str(path.relative_to(root)),revision='worktree')
 for prefix,revision in branches.items():
  if module.split('.')[-1].startswith(prefix):
   path='docs/research/v8-r0-zk-20261009/lean/'+rel
   result=subprocess.run(['git','show',revision+':'+path],cwd=root,capture_output=True)
   if result.returncode==0:return result.stdout,dict(path=path,revision=revision,method='git show; read only')
 return None,None

def visit(module):
 if module in entries:return
 content,origin=get(module)
 if content is None:
  entries[module]=dict(source_available=False)
  if module.startswith(('R1Z.','R0Z.','R0P.','R1J.','PDict_')):missing.append(module)
  return
 text=content.decode();imports=[m for line in text.splitlines() if line.startswith('import ') for m in line[7:].split()]
 entries[module]=dict(source_available=True,sha256=hashlib.sha256(content).hexdigest(),origin=origin,imports=imports)
 for child in imports:visit(child)

audit='R1Z.PV_Join_FinalAudit';visit(audit);audit_names=set(entries)
new=['Current71','Current100','Current101','EmbeddingWord','Embedding','CB3Flat','CB3Boundary','HeapCompatibility','PublicOp20','AuditProjection','LedgerSource']
for name in new:visit('R1Z.PV_Join_'+name)
objects=subprocess.check_output(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90',
 'find /home/dombarker/project-offloads/aspis-joint-20261019/objects -name "*.olean" -printf "%P\\n"'],text=True)
available={p.removesuffix('.olean').replace('/','.') for p in objects.splitlines()}
for name,row in entries.items():row['restored_object_present']=name in available
out=dict(kind='compile-free source/import preflight; not declaration closure or coherence certification',
 revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 sibling_revisions=branches,audit_root=audit,audit_local_source_modules=len(audit_names),
 audit_missing_restored_objects=sorted(name for name in audit_names if entries[name]['source_available'] and name not in available),
 missing_R_sources=sorted(set(missing)),modules=entries,compiler_invoked=False,attempt_ids=None)
path=root/'evidence/pv-join-20261026/resume/source-preflight.json';path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(audit_local_source_modules=out['audit_local_source_modules'],audit_missing_restored_objects=len(out['audit_missing_restored_objects']),missing_R_sources=out['missing_R_sources']),indent=2))
