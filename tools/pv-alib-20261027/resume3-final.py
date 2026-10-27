"""Freeze the final three-row audit and V184 cached replay once leaves pass."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean';j=json.loads((E/'resume3-project-preflight.json').read_text());sources=j['sources'];seen=set();ordered=[]
def visit(m):
 if m in seen or m not in sources:return
 seen.add(m)
 for x in sources[m]['imports']:visit(x)
 ordered.append(m)
visit('R1Z.PV_AL_MoveClosure');names=set(json.loads((E/'resume3-candidate-cone.json').read_text())['axioms'])
for m in ordered:
 if not m.startswith('R1Z.PV_AL_'):continue
 s=(R/sources[m]['path']).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)
 if not ns:continue
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):names.add(n if n.startswith(('R1Z.',ns[1]+'.')) else ns[1]+'.'+n)
audit=L/'R1Z/PV_AL_FinalRowsAudit.lean';audit.write_text('-- Final combined candidate audit: V184, V233 and V265.\n'+''.join('import '+x+'\n' for x in ['R1Z.PV_AL_MoveClosure','R1Z.PV_AL_SplitBridge','R1Z.PV_AL_CircleSelected'])+''.join('#print axioms '+n+'\n' for n in sorted(names)))
p=L/'R1Z/PV_AL_MoveReplay.lean';p.write_text('-- One focused V184 replay, on the pinned cached dependency cone.\n'+''.join('import '+x+'\n' for x in ordered)+''.join('#print axioms R1Z.PV_AL_MoveClosure.'+n+'\n' for n in ['complete','allocation_delta','nonvacuous']))
(E/'resume3-final-cone.json').write_text(json.dumps(dict(v184_sources={m:sources[m] for m in ordered},audit_names=sorted(names),audit_sha256=hashlib.sha256(audit.read_bytes()).hexdigest(),v184_replay_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='focused cached candidate cones, no full manifest/deployment replay'),indent=2)+'\n')
print(len(ordered),'V184 modules;',len(names),'combined axiom queries')
