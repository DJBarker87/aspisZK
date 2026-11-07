from NLW_audit import *
import subprocess
for i in range(8):
 r=json.loads((E/'NLW_audit'/('batch'+str(i))/('proof'+str(i)+'.json')).read_text())
 assert r['exit_status'] in [0,1]
 assert all(set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in r['results'])
r=run('NLW_L081','lean','NLW_064CandidateFold');assert r['exit_status']==0
subprocess.run([sys.executable,str(E/'NLW_extend_gate.py')],check=True)
r=run('NLW_L082','lean','NLW_COMBINED_IMPORT');assert r['exit_status']==0
r=audit('NLW_L083','audit','scan');assert r['exit_status']==0
r=audit('NLW_L084','audit','batch8')
assert r['exit_status'] in [0,1]
subprocess.run([sys.executable,str(E/'NLW_finalize_audit.py')],check=True)
rows=[json.loads(l) for l in (E/'NLW_ATTEMPTS.jsonl').read_text().splitlines()]
extra={n:(E/n).read_text() for n in ['NLW_export.py','NLW_retention.py','NLW_MODULES.json']}
extra['NLW_ATTEMPTS_INDEX.json']=json.dumps([dict(attempt=r['attempt'],kind=r['kind']) for r in rows])
r=run('NLW_L085','inspect','NLW_retention',['python3','NLW_retention.py'],extra)
assert r['exit_status']==0
subprocess.run([sys.executable,str(E/'NLW_finalize_audit.py')],check=True)
