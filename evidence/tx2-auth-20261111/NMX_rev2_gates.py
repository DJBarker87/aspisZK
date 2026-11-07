"""Own new-root audit and one combined import; unchanged baseline is not rerun."""
from NMX_formal import *
env=json.loads((E/'NMX_REV2_ENV.json').read_text())
subprocess.run(['python3',str(E/'NMX_rev2_prepare_gates.py')],check=True)
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
n=900
first=json.loads((E/'NMX_REV2_AUDIT_ROOTS.json').read_text())['first_new_group']
for i in range(first,first+2):
 while (E/('NMX_L'+str(n)+'.json')).exists():n+=1
 files={'NMX_batch.py':(E/'NMX_batch.py').read_text(),'NMX_AUDIT_ROOTS.json':(E/'NMX_REV2_AUDIT_ROOTS.json').read_text(),'NMX_AUDIT_MODULES.json':(E/'NMX_REV2_AUDIT_MODULES.json').read_text()}
 r=run('NMX_L'+str(n),'audit','proof'+str(i),['python3','NMX_batch.py','proof'+str(i)],files,env_extra=env);n+=1
 assert r['exit_status']==0,'STOP own new-root audit failed'
while (E/('NMX_L'+str(n)+'.json')).exists():n+=1
r=run('NMX_L'+str(n),'lean','NMX_R2_COMBINED_IMPORT',env_extra=env)
assert r['exit_status']==0,'STOP focused combined import failed'
