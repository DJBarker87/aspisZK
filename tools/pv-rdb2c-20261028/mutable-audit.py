from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb2c-20261028';rows=[]
for n in ['PV_RDB2C_PV_B2_C_ConstructorEnvironment','PV_RDB2C_PV_B2_C_MutationStep','PV_RDB2C_PV_B2_C_MutationLoop','PV_RDB2C_PV_B2_C_RawWeights251Funs']:
 p=P/(n+'.lean');s=p.read_text()
 defs=list(re.finditer(r'^(?:noncomputable )?def\s+([^\s(]+)',s,re.M))
 for i,m in enumerate(defs):
  text=s[m.start():defs[i+1].start() if i+1<len(defs) else len(s)]
  bound=re.findall(r'let\s+\([^\n]*?\b([A-Za-z0-9_]*back[0-9_]*)\)\s*←',text)
  uses={v:len(re.findall(r'\b'+re.escape(v)+r'\b',text)) for v in bound}
  discarded=re.findall(r'let\s+\([^\n]*,\s*_\)\s*←[^\n]*(?:mut|next|iter)',text)
  if uses or discarded:
   rows.append(dict(module='R1Z.'+n,function=m[1],source_sha256=hashlib.sha256(s.encode()).hexdigest(),backward_handles=uses,handles_used_more_than_once=all(c>=2 for c in uses.values()),discarded_mutable_result_patterns=discarded,scope='lexical per-function preflight; complete restoration is certified by replayed loop/source theorems, not this count alone'))
assert all(r['handles_used_more_than_once'] and not r['discarded_mutable_result_patterns'] for r in rows)
(E/'mutable-restoration-audit.json').write_text(json.dumps(rows,indent=2)+'\n');print([(r['module'],len(r['backward_handles'])) for r in rows])
