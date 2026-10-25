#!/usr/bin/env python3
"""Read-only sizes for the remaining caller obligations, not proof-completeness scores."""
from pathlib import Path
import hashlib,json,re,sys
root=Path(__file__).resolve().parents[2]
base=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'
src=base/'ProverRwFullFuns.lean';text=src.read_text()
starts=list(re.finditer(r'(?m)^def\s+([\w.]+)',text));decls={}
for i,m in enumerate(starts):
 end=text.find('\n/--',m.end());end=len(text) if end<0 else end
 if i+1<len(starts):end=min(end,starts[i+1].start())
 body=text[m.start():end].rstrip()
 decls[m[1]]=dict(body=body,lines=len(body.splitlines()),line=text[:m.start()].count('\n')+1,sha256=hashlib.sha256(body.encode()).hexdigest())
ext=(base/'ProverRwFullExternalFuns.lean').read_text();types=(base/'ProverRwFullExternalTypes.lean').read_text()
aliases={m[1]:int(m[2]) for m in re.finditer(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalFuns\.op(\d+)',ext)}
functions=set(map(int,re.findall(r'(?m)^  op(\d+)(?=\s|\(|\{)',ext)))
typeids=set(map(int,re.findall(r'(?m)^  op(\d+)(?=\s|\(|\{)',types)))
tokens=lambda body:set(re.findall(r'[\w]+(?:\.[\w]+)+',body))
def graph(name):
 seen=set();ops=set();todo=[name]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  refs=tokens(decls[n]['body'])-{n}
  todo.extend((refs&decls.keys())-seen)
  ops.update(aliases[x] for x in refs&aliases.keys())
 return seen,ops
names=['prover.prove_masked_with_attempt','prover.prove_masked_attempt','prover.derive_private_salts','host_semantic.build_with_material','prover.prepare_opening','prover.finish_opening','prover.public_check','prover.publish_compact','host_transcript.Transcript.queries','prover.retry_attempt']
rows=[]
for name in names:
 ds,ops=graph(name);d=decls[name]
 rows.append(dict(declaration=name,source_line=d['line'],direct_lines=d['lines'],source_sha256=d['sha256'],transitive_emitted_declarations=len(ds),transitive_emitted_lines=sum(decls[n]['lines'] for n in ds),referenced_external_function_ids=sorted(ops),referenced_external_function_count=len(ops),scope='Syntactic declaration-reference overapproximation; overlapping rows, not remaining proof counts.'))
x=dict(source=str(src.relative_to(root)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),emitted_declarations=len(decls),dictionary=dict(function_entries=len(functions),installed_preexisting=[233,248],newly_installed=[],remaining_entries=sorted(functions-{233,248}),remaining_count=len(functions-{233,248}),type_entries=len(typeids)),components=rows,root_obligation=dict(name='ProverCommitDeployedFuel22.RustProverRefinement conjunct 1',quantifiers='every adversary and every witness with h.public w=x.1',remaining=['native effect/extraction adequacy and E1/E2 joint laws','whole remaining per-attempt body/model equation and PrefixContract/BodyContract instances','complete experiment/observer/ordered shared-oracle RunJoin.cp and RunJoin.agreement'],unchanged=True),warning='Local query/control obligations closed by kernel theorems; global dictionary counts are not reduced by helper proofs or caller copies.')
Path(sys.argv[1]).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(dictionary=x['dictionary']|{'remaining_entries':'omitted'},components=[{k:r[k] for k in ['declaration','direct_lines','transitive_emitted_declarations','transitive_emitted_lines','referenced_external_function_count']} for r in rows]),indent=2))
