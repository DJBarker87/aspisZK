from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean'
j=json.loads((E/'resume3-project-preflight.json').read_text());sources=j['sources'];seen=set()
def visit(m):
 if m in seen or m not in sources:return
 for x in sources[m]['imports']:visit(x)
 seen.add(m)
for m in ['R1Z.PV_AL_SplitBridge','R1Z.PV_AL_CircleSelected']:visit(m)
names=[]
for m in sorted(seen):
 if not m.startswith('R1Z.PV_AL_'):continue
 s=(R/sources[m]['path']).read_text(); ns=re.search(r'^namespace (\S+)',s,re.M)
 if not ns:continue
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):names.append(n if n.startswith(('R1Z.',ns[1]+'.')) else ns[1]+'.'+n)
imports=['R1Z.PV_AL_SplitBridge','R1Z.PV_AL_CircleSelected']
p=L/'R1Z/PV_AL_Rows233265Audit.lean';p.write_text('-- Combined closing-theorem audit for both provisional rows.\n'+''.join('import '+x+'\n' for x in imports)+''.join('#print axioms '+x+'\n' for x in sorted(set(names))))
p=L/'R1Z/PV_AL_Rows233265Replay.lean';p.write_text('-- One candidate dependency-cone replay against verified cached objects.\n-- No deployed endpoint or whole manifest replay is claimed.\n'+''.join('import '+x+'\n' for x in sorted(seen))+''.join('#check @'+x+'\n' for x in ['R1Z.PV_AL_SplitSelected.native_callback','R1Z.PV_AL_SplitSelected.consumed','R1Z.PV_AL_SplitBridge.source_reference','R1Z.PV_AL_SplitBridge.consumed_reassembles','R1Z.PV_AL_CircleNative.source_reference','R1Z.PV_AL_CircleSelected.native_source','R1Z.PV_AL_CircleSelected.consumed']))
(E/'resume3-candidate-cone.json').write_text(json.dumps(dict(roots=imports,sources={m:sources[m] for m in sorted(seen)},axioms=sorted(set(names)),scope='cached candidate dependency closure only'),indent=2)+'\n')
print(len(seen),'project modules',len(set(names)),'axiom queries')
