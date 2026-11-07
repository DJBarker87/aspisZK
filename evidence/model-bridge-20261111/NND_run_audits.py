from NND_formal import *
# Every child has an independent capped scope, disk/share/admission and full receipt.
ids=list(range(272,301))+[17,18,19]
jobs=[(270,'planted'),(271,'mutations')]+list(zip(ids,('proof'+str(i) for i in range(32))))
if len(sys.argv)>1:jobs=[(int(sys.argv[1]),sys.argv[2])]
for n,mode in jobs:
 a=f'NND_L{n:03}'
 files={name:(E/name).read_text() for name in ['NND_audit_run.py','NND_AUDIT_ROOTS.json','NND_AUDIT_MODULES.json']}
 r=run(a,'audit',mode,command=['python3','NND_audit_run.py',mode,a],extra=files)
 if r['exit_status']:sys.exit(r['exit_status'])
