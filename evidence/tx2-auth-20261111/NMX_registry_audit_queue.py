from NMX_formal import *
x=json.loads((E/'NMX_234_AUDIT_ROOTS.json').read_text());first=x['first_new_group']
for i in range(first,len(x['groups'])):
 files={'NMX_batch.py':(E/'NMX_batch.py').read_text(),'NMX_AUDIT_ROOTS.json':(E/'NMX_234_AUDIT_ROOTS.json').read_text(),'NMX_AUDIT_MODULES.json':(E/'NMX_234_AUDIT_MODULES.json').read_text()}
 r=run('NMX_L'+str(1050+i-first),'audit','proof'+str(i),['python3','NMX_batch.py','proof'+str(i)],files)
 assert r['exit_status']==0,'STOP own raw axiom audit failed'
