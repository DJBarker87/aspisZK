"""Split only failed audit 7909's incompatible import union; never replay that union."""
from pathlib import Path
src=Path(__file__).with_name('audit-continuation.py').read_text()
prologue='''import json,re,hashlib,subprocess,time
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');D=J/'evidence-S';T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');O=J/'objects-S'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
man=json.loads((D/'manifest-S.json').read_text());mods={e['module']:e for e in man['order']}
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 if m in mods:
  for dep in mods[m]['imports']:closure(dep,seen)
 return seen
bad=next(r for r in map(json.loads,(D/'continuation-axioms-batches.jsonl').read_text().splitlines()) if r['attempt']==7909)
assert bad['exit']!=0
pair={'AspisR1PublicSerializer.Types','AspisR1RecordParser.Types'}
groups={'serializer':[],'record-parser':[],'neutral':[]}
for m in bad['requested_modules']:
 c=closure(m);assert not pair<=c
 key='serializer' if 'AspisR1PublicSerializer.Types' in c else 'record-parser' if 'AspisR1RecordParser.Types' in c else 'neutral';groups[key].append(m)
batches=[(k,ms,False) for k,ms in groups.items() if ms]
rep=json.loads((D/'collision-closures.json').read_text());rep['additional_audit_collision']={'declaration':'instDiscriminantErrorIsize','owners':sorted(pair),'failed_audit_attempt':7909,'roots_requiring_both':[m for m in man['roots'] if pair<=closure(m)],'repair_partitions':groups};(D/'collision-closures.json').write_text(json.dumps(rep,indent=2)+'\\n')
'''
body=src[src.index('for i,(partition,batch,external) in enumerate(batches):'):]
body=body.replace('SoundnessClosureAuditContinuation','SoundnessClosureAuditCollisionRepair').replace('a=7900+i','a=7960+i')
# The actual generated driver is retained before execution for review.
out=Path(__file__).with_name('audit-collision-repair-driver.py');out.write_text(prologue+body)
exec(compile(out.read_text(),str(out),'exec'))
