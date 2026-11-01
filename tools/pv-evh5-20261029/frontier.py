"""Read-only textual source-reference census; never a transitive fidelity proof."""
from pathlib import Path
import re,json,hashlib,subprocess
E=Path('evidence/pv-evh5-20261029');rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
e=subprocess.check_output(['git','show',rev+':'+p.replace('Funs.lean','ExternalFuns.lean')],text=True)
def declarations(text):
 matches=list(re.finditer(r'(?m)^(?:def|abbrev)\s+([^\s:({]+)',text));out={}
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else len(text)
  body=text[m.end():end].split('/--',1)[0]
  out[m[1]]=body
 return out
D=declarations(s);X=declarations(e);aliases={k:re.search(r'ExternalFuns\.(op\d+)',v)[1] for k,v in X.items() if re.search(r'ExternalFuns\.(op\d+)',v)}
allnames=set(D)|set(aliases)
pattern=re.compile(r'(?<![\w.])(?:'+ '|'.join(re.escape(n) for n in sorted(allnames,key=len,reverse=True))+r')(?![\w.])')
edges={k:sorted(set(pattern.findall(v))- {k}) for k,v in D.items()}
roots=['RealR1_client.prove_for_proof_accounts','prover.prove_masked_attempt'];pending=roots.copy();seen=set()
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);pending.extend(edges.get(n,[]))
accepted={json.loads(q.read_text())['target'] for q in E.glob('receipt-*.json') if json.loads(q.read_text())['accepted']}
expanded={}
for q in E.glob('*-generation.json'):
 x=json.loads(q.read_text());mod='PV_EVH_'+q.name.removesuffix('-generation.json')
 if mod in accepted and 'function' in x:expanded[x['function']]=mod
ext={k:aliases[k] for k in sorted(seen & set(aliases))}
r=dict(scope='TEXTUAL source-reference census only; dictionary dispatch and callback reachability may add edges. This is not native event coverage, source association or a closure theorem.',source_revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),roots=roots,textually_reached_source_declarations=len(seen & set(D)),textually_reached_external_aliases=len(ext),accepted_generated_spines_on_textual_cone={k:v for k,v in expanded.items() if k in seen},external_frontier=ext,source_frontier=sorted((seen & set(D))-set(expanded)),rows_removed=[])
(E/'source-reference-frontier.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['textually_reached_source_declarations','textually_reached_external_aliases']}))
