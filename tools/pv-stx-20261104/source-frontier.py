"""Reproducible declaration-reference overapproximation; NOT a reachability proof."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path('evidence/pv-stx-20261104');rev='fd4a644fd414079022f8781c14a6683b41504ab7'
D='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'
raw={n:subprocess.check_output(['git','show',rev+':'+D+n]).decode() for n in ['ProverRwFullFuns.lean','ProverRwFullExternalFuns.lean']}
def strip(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  pair=s[i:i+2];c=s[i]
  if depth:
   if pair=='/-':depth+=1;out.extend('  ');i+=2;continue
   if pair=='-/':depth-=1;out.extend('  ');i+=2;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if string:
   if c=='\\':out.extend('  ');i+=2;continue
   if c=='"':string=False
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if pair=='/-':depth=1;out.extend('  ');i+=2;continue
  if pair=='--':
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j;continue
  if c=='"':string=True;out.append(' ');i+=1;continue
  out.append(c);i+=1
 assert not depth and not string
 return ''.join(out)
s=strip(raw['ProverRwFullFuns.lean']);matches=list(re.finditer(r'^def\s+([A-Za-z0-9_.]+)',s,re.M));defs={}
for i,m in enumerate(matches):
 end=matches[i+1].start() if i+1<len(matches) else len(s)
 defs[m[1]]=s[m.end():end]
external={m[1]:m[2] for m in re.finditer(r'^abbrev (\S+).*?@ExternalFuns\.(op\d+)',raw['ProverRwFullExternalFuns.lean'],re.M)}
allnames=set(defs)|set(external)
graph={n:sorted(set(re.findall(r'(?<![A-Za-z0-9_.])([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)+)',v))&allnames) for n,v in defs.items()}
root='RealR1_client.prove_for_proof_accounts';seen=set();pending=[root]
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);pending += graph.get(n,[])
covered=json.loads((E/'entropy-generation.json').read_text())['definitions']
coverage={v['source_name'] for v in covered}
callbacks=[n for n in seen if 'CoreOpsFunction' in n]
result=dict(source_revision=rev,source_files={n:hashlib.sha256(v.encode()).hexdigest() for n,v in raw.items()},classification='Textual declaration-reference overapproximation; signatures included; dynamic callback targets unresolved; not a source reachability/fidelity theorem',root=root,declared_definitions=len(defs),reachable_definitions=sorted(seen&set(defs)),referenced_external_aliases=[dict(name=n,field=external[n]) for n in sorted(seen&set(external))],callback_definitions=sorted(callbacks),lifted_entropy_definitions=sorted(coverage),unlifted_definitions=sorted((seen&set(defs))-coverage),graph={n:graph[n] for n in sorted(seen&set(defs))},mandatory_warnings=['Higher-order trait callbacks must retain source receiver/capture and effect code','Native interpretation cannot treat op259 as a completed pure callback','Aeneas simplify_duplicate_calls and default no-op drops require reached-source review before native trace credit','No source_entry_world or RuntimeBinding projection is supplied by this inventory'])
p=E/'source-frontier.json';p.write_text(json.dumps(result,indent=2)+'\n')
print(len(result['reachable_definitions']),'referenced definitions;',len(result['referenced_external_aliases']),'external aliases;',len(result['callback_definitions']),'callback declarations')
