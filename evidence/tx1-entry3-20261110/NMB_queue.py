from NMB_formal import run
import sys
for spec in sys.argv[1:]:
 a,module=spec.split(':',1)
 r=run('NMB_L'+a,'lean',module)
 if r['exit_status']:sys.exit(r['exit_status'])
