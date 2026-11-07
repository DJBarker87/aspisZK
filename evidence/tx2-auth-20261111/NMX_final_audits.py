from NMX_formal import *
groups=json.loads((E/'NMX_AUDIT_ROOTS.json').read_text())['groups']
for i in range(4,len(groups)):
 files={n:(E/n).read_text() for n in ['NMX_batch.py','NMX_AUDIT_ROOTS.json','NMX_AUDIT_MODULES.json']}
 r=run(f'NMX_L{400+i:03d}','audit','proof'+str(i),['python3','NMX_batch.py','proof'+str(i)],files)
 if r['exit_status']:raise RuntimeError('STOP raw audit failed; no unchanged rerun')
