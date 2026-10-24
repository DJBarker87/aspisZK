"""Read-only inventory of retained job evidence, never other worktrees."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023'
rows={}
def scan(value,path,key):
    if isinstance(value,list):
        if '-backend' in value and all(isinstance(x,str) for x in value):
            i=value.index('-backend')
            if i+1<len(value) and value[i+1]=='lean':
                h=hashlib.sha256(json.dumps(value).encode()).hexdigest()
                row=rows.setdefault(h,dict(command=value,all_flags=value[1:],explicit_eval_drops='-eval-drops' in value,receipts=[]))
                row['receipts'].append(dict(path=str(path.relative_to(E)),json_key=key,sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        else:
            for i,v in enumerate(value):scan(v,path,key+'/'+str(i))
    elif isinstance(value,dict):
        for k,v in value.items():scan(v,path,key+'/'+k)
for p in E.rglob('*.json'):
    if 'native-drop-abi' in p.parts or p.stat().st_size>5_000_000:continue
    try:scan(json.loads(p.read_text()),p,'')
    except (UnicodeDecodeError,json.JSONDecodeError):continue
out=dict(schema='ProverRwNativeDropABI-retained-extraction-inventory-v1',
         scope='Only retained prover-rw-20261023 evidence in assigned worktree; commands found recursively, no inferred missing commands; not an audit of live worktrees or installed backend.',
         config_sha256='81dd9fdb863e2c5e05407991f680a1a3c33eb01c289bf309a67a6f50fa66b35d',
         assessment='For source associated with pinned Config default true, absent -eval-drops leaves no-op mode; explicitly enabled mode alone does not establish cleanup semantics. Other source associations remain unknown unless separately pinned. Charon --precise-drops describes emitted LLBC, not evaluation in Aeneas.',
         commands=list(rows.values()))
(E/'native-drop-abi/extraction-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(unique_commands=len(rows),explicit=sum(r['explicit_eval_drops'] for r in rows.values()),omitted=sum(not r['explicit_eval_drops'] for r in rows.values()))))
