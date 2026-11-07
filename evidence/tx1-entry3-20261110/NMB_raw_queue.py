from NMB_audit import *
start=int(sys.argv[1])if len(sys.argv)>1 else 0
groups=json.loads((E/'NMB_AUDIT_ROOTS.json').read_text())['groups'];assert len(groups)==53
for i in range(start,len(groups)):audit(f'NMB_L{83+i:03d}','proof'+str(i))
