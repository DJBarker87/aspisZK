from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume5';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-[0-9]*.json'))];good=[r for r in rows if r['accepted']]
assert len(rows)==62 and len(good)==61
contexts=[];core=[];mods=set();names=set()
for r in good:
 mods.add(r['target'])
 for s in r['axioms']:
  n=re.match(r"'([^']+)'",s)[1];names.add(n)
  if n.startswith(('R1Z.PV_RE_ComposedContext.','R1Z.PV_RE_ComposedContext5.','R1Z.PV_RE_ComposedContext6.')):contexts.append(n)
  else:core.append(n)
old=json.loads((E.parent/'resume4/accepted-source-pins.json').read_text());old=[r for r in old if 'ComposedChunk' in r['module']]
old.append(dict(module='R1Z/PV_RE_ComposedChunk003'))
for r in old:mods.add(r['module'])
contextMods={m for m in mods if 'ComposedChunk' in m or 'Exceptional' in m}
contextNames=sorted(set(contexts));coreNames=sorted(set(core))
a='\n'.join('import '+m.replace('/','.') for m in sorted(contextMods))+'\n'+'\n'.join('#print axioms '+n for n in contextNames)+'\n'
b='import R1Z.PV_RE_Exceptional6\n'+'\n'.join('import '+m.replace('/','.') for m in sorted(mods-contextMods))+'\n'+'\n'.join('#print axioms '+n for n in coreNames)+'\n'
b+='\n#print R1Z.PV_RE_EntropyBoundaryFrames.retry_failure\n#print R1Z.PV_RE_LiteralShape5.legacy_success\n'
for n in contextNames:
 if '.literalShape' in n or '.literalSuccess' in n:b+='#print '+n+'\n'
c='import R1Z.PV_RE_FinalAudit5A\nimport R1Z.PV_RE_FinalAudit5B\n-- One final frozen new-proof manifest import replay, not a release rebuild.\n#check R1Z.PV_RE_EntropyBoundaryFrames.trait_failure\n#check R1Z.PV_RE_LiteralShape5.legacy_success\n'
for label,s in [('A',a),('B',b),('C',c)]:
 (L/f'PV_RE_FinalAudit5{label}.lean').write_text(s)
manifest=[]
for m in sorted(mods):
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');manifest.append(dict(module=m,path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(sources=manifest,audited_new_theorems=sorted(names),context_axioms=len(contextNames),core_axioms=len(coreNames),full_source_invocation_coverage=False,compiled_source_chunks=list(range(64)),uncompiled_original_chunks=list(range(64,74)),exceptional_generator6_named_shapes=[n for n in names if '.literal' in n]),indent=2)+'\n')
print(len(mods),'frozen modules;',len(contextNames),'context axioms;',len(coreNames),'core axioms')
