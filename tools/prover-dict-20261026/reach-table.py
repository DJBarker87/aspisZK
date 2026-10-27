"""Read-only dependency witnesses and explicitly scoped caller obligations.
A reference path is an overapproximation, never a proof of feasible execution.
"""
from pathlib import Path
import hashlib,json,re
from collections import deque
r=Path(__file__).resolve().parents[2]
b=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026'
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(b/'ProverRwFullFuns.lean').read_text()
# Strip nested comments, line comments and string literals without introducing tokens.
out=[];i=0;depth=0;quote=False
while i<len(s):
 pair=s[i:i+2];c=s[i]
 if not quote and pair=='/-':depth+=1;i+=2;continue
 if depth and pair=='-/':depth-=1;i+=2;continue
 if depth:
  out.append('\n' if c=='\n' else ' ');i+=1;continue
 if not quote and pair=='--':
  end=s.find('\n',i);i=len(s) if end<0 else end;continue
 if c=='"' and (i==0 or s[i-1]!='\\'):quote=not quote;out.append(' ');i+=1;continue
 out.append(' ' if quote else c);i+=1
s=''.join(out);ms=list(re.finditer(r'(?m)^def\s+([\w.]+)',s))
d={m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
a={m[1]:int(m[2]) for m in re.finditer(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalFuns\.op(\d+)',(b/'ProverRwFullExternalFuns.lean').read_text())}
root='RealR1_client.prove_for_proof_accounts';paths={root:[root]};todo=deque([root]);witness={}
while todo:
 n=todo.popleft();refs=set(re.findall(r'\b\w+(?:\.\w+)+',d[n]))
 for alias in sorted(refs&a.keys()):witness.setdefault(a[alias],paths[n]+[alias])
 for child in sorted(refs&d.keys()):
  if child not in paths:paths[child]=paths[n]+[child];todo.append(child)
old=json.loads((e/'installed-and-remaining.json').read_text());rows=[]
for z in old['functions']:
 i=z['id'];proof='R1Z.PDict_ClientFormatterIndependent.client_erased' if i==85 else None
 rows.append(dict(id=i,name=z['name'],predecessor_status=z['status'],reference_path=witness.get(i),syntactic_reference_reachable=i in witness,execution_reachable='no source dependence (existing full caller equality)' if i==85 else 'not established',theorem=proof,required_now=i!=85,qualification='Reference path is not an executable witness; pending multi-field proof is not accepted as full caller evidence.'))
summary=dict(root=root,source_sha256={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in b.glob('ProverRwFull*.lean')},source_functions=len(paths),reference_fields=len(witness),reference_absent=sorted(set(range(262))-witness.keys()),historical=dict(selected=163,open=99,denominator=262),proved_source_requirements=dict(selected=163,open=98,denominator=261,removed=[85]),pending_if_multi_field_caller_bridge_passes=dict(selected=159,open=96,denominator=255),types=[dict(id=3,name='std.io.error.Error',status='retained: File error results and kind consumed; no owned-reference/native transport yet'),dict(id=27,name='core.fmt.Formatter',status='retained type transport: op85 erased; changing carrier also changes generic trait dictionaries; J20600/J20601 rejected')],operations=rows,root_premises_removed=0,target_established=False)
(e/'reach206/reachability.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Caller dictionary reachability checkpoint','','This is a partial Stage 1 checkpoint. Target not yet established. No positive execution-reachability theorem is claimed from a reference graph.','','Historical: 163 selected / 99 open / 262 fields. Existing complete op85 erasure justifies 163 selected / 98 open / 261 source fields. The new seven-field bridge is NOT checked: 159 / 96 / 255 is a pending bound, not the final required denominator. Types remain 26 / 28; File ownership/world remains open.','','Named premise effect: op85 source callback equality is unnecessary by the inherited `R1Z.PDict_ClientFormatterIndependent.client_erased`. New helper checks do not yet discharge op16/op18 at the full caller. Root RustProverRefinement conjunct 1 is retained unchanged.','','## All 99 predecessor-open operations','','| Op | Name | Reference path? | Execution classification / theorem |','|---:|---|---|---|']
for z in rows:
 if z['predecessor_status']!='OPEN':continue
 status='No source dependence: `'+z['theorem']+'`' if z['theorem'] else ('Unresolved: reference path only' if z['syntactic_reference_reachable'] else 'Unresolved: absent; caller bridge pending')
 lines.append(f"|{z['id']}|`{z['name']}`|{'yes' if z['syntactic_reference_reachable'] else 'no'}|{status}|")
lines+=['','## Open types','','| Type | Representation | Status |','|---:|---|---|']
for z in summary['types']:lines.append(f"|{z['id']}|`{z['name']}`|{z['status']}|")
lines+=['','Reference paths and source hashes: `reachability.json`. Lean raw inputs, diagnostics, time, dependencies and axioms: `206*-receipt.json` / `lean-summary.json`. No Kani run, production change, native error/world law, or frozen release replay is claimed.']
(e/'reach206/REACHABILITY.md').write_text('\n'.join(lines)+'\n')
print(summary['reference_absent']);print('table rows',sum(z['predecessor_status']=='OPEN' for z in rows))
