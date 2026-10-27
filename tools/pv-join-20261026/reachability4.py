"""Compile-free extracted call graph. This is an overapproximation, never a trace."""
from pathlib import Path
import re,json,hashlib,subprocess,collections
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume4';p=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'
raw=(p/'ProverRwFullFuns.lean').read_text();s=re.sub(r'/\-.*?\-/','',raw,flags=re.S)
ms=list(re.finditer(r'^def\s+([^\s{(:]+)',s,re.M));d={m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
pat=re.compile(r'(?<![\w.])(?:'+'|'.join(re.escape(n) for n in sorted(d,key=len,reverse=True))+r')(?![\w.])');g={n:sorted(set(pat.findall(b))) for n,b in d.items()}
root='RealR1_client.prove_for_proof_accounts';paths={root:[root]};q=collections.deque([root])
while q:
 n=q.popleft()
 for c in g[n]:
  if c not in paths:paths[c]=paths[n]+[c];q.append(c)
rows=json.loads((r/'evidence/pv-join-20261026/resume/remaining-inventory.json').read_text())['remaining_without_joined_source_law'];entries=[]
for line in (p/'ProverRwFullExternalFuns.lean').read_text().splitlines():
 m=re.match(r'abbrev (.*?) .*:= @ExternalFuns.op(\d+) ',line)
 if not m or int(m[2]) not in rows:continue
 name=m[1];callers=[n for n,b in d.items() if re.search(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',b)]
 entries.append(dict(op=int(m[2]),extracted_name=name,callers=callers,static_paths=[paths[n]+[name] for n in callers if n in paths],execution_reached='unresolved',universal_fixture_unreachability='not proved'))
siblings={b:subprocess.check_output(['git','rev-parse',b],text=True).strip() for b in ['codex/cx-prover-rw-20261023','codex/pv-cb-20261026','codex/pv-cb3-20261026']}
x=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),root=root,root_variant='S2',kind='syntactic overapproximation: function and trait construction edges; no execution claim',static_inventory=rows,entries=entries,sibling_revisions=siblings,fixtures={f:dict(reached_set=None,unreachable_on_all_admitted_inputs=[],reason='Fixture preparation does not fix entropy, nonce-store admission or oracle/error behavior. A static path is not an execution witness.') for f in ['transfer','withdrawal']},model_instance_available=False)
(e/'source-reachability.json').write_text(json.dumps(x,indent=2)+'\n')
print('30/30 static paths; no fixture execution reachability credit')
