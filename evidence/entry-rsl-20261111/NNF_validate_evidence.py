"""Validate own proof evidence without a prover replay."""
from pathlib import Path
import hashlib,json,lzma,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[]
for p in sorted(E.glob('NNF_L[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());receipts.append(x)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 ad=json.loads((E/(x['attempt']+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 if x['kind']=='lean' and x['exit_status']==0:
  for line in x['print_axioms']:
   if 'depends on axioms:' in line:
    assert set(re.search(r'\[(.*)\]',line)[1].split(', '))<=allowed,line
assert len(receipts)<=150
assert not any(x['kind'] in ['kani','extract'] for x in receipts)
expected=[r for group in json.loads((E/'NNF_AUDIT_ROOTS.json').read_text())['groups'] for r in group]
results=[]
for p in sorted((E/'NNF_audit').glob('proof*/proof*.json')):
 x=json.loads(p.read_text());assert x['exit_status']==0
 results+=x['results']
assert sorted(expected)==sorted(x['root'] for x in results)
for x in results:
 assert x['equal'] and set(x['walked_axioms'])<=allowed,x
assert len(expected)==len(set(expected))
# Own Lean sources: every proof theorem is in the audit and printed locally.
source_theorems=[]
for name in ['NNF_Carrier','NNF_Dispatch','NNF_Reify','NNF_Folds','NNF_TAS']:
 text=(E/(name+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M)
 for thm in re.findall(r'^theorem (\w+)',text,re.M):
  assert '#print axioms '+thm in text
  source_theorems.append(name+'.'+thm)
 latest=next(x for x in reversed(receipts) if x['module']==name)
 assert latest['exit_status']==0
 assert sha(text.encode())==latest['source_hashes']['NNF_generated/'+name+'.lean']
assert sorted(source_theorems)==sorted(expected)
# Lossless archives and exact source input snapshots.
pairs=0
for p in E.rglob('*.sha256'):
 original=p.with_suffix('');arch=Path(str(original)+'.xz')
 assert arch.exists(),str(arch)
 assert sha(lzma.decompress(arch.read_bytes()))==p.read_text().strip(),str(p)
 pairs+=1
idx=json.loads((E/'NNF_INPUTS.json').read_text())
for h,x in idx['objects'].items():
 raw=lzma.decompress((E/x['path']).read_bytes());assert sha(raw)==h and len(raw)==x['bytes']
 assert sha((E/x['path']).read_bytes())==x['archive_sha256']
for rc in receipts:
 snap=idx['attempts'].get(rc['attempt'],{})
 assert snap==rc['source_hashes'],rc['attempt']
 for h in snap.values():assert h in idx['objects']
assert all(x['free_bytes']>=40_000_000_000 for x in [json.loads(l) for l in (E/'NNF_DISK.jsonl').read_text().splitlines()] if x['retry']==0)
assert not list(p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000)
assert json.loads((E/'NNF_L021/receipt.json').read_text())['exit_status']==0
assert json.loads((E/'NNF_L022/receipt.json').read_text())['exit_status']==124
assert json.loads((E/'NNF_L028/receipt.json').read_text())['exit_status']==0
ret=json.loads((E/'NNF_RETENTION.json').read_text());assert ret['deletions']==0
x={'status':'PASS','receipts':len(receipts),'own_proof_theorems':len(expected),'raw_ax2_standard_only':True,'collector_agreement':True,'sha_pairs':pairs,'source_snapshot_objects':len(idx['objects']),'source_snapshot_attempts':len(idx['attempts']),'all_limits_verified':True,'combined_import':'NNF_L021 PASS','retention':'NNF_L023/L024/L025 split pins and NNF_L028 PASS','new_Kani':0,'new_extraction':0}
(E/'NNF_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
