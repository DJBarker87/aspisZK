from NLW_formal import *
import sys
for a,module in zip(sys.argv[1::2],sys.argv[2::2]):
 rc=run(a,'lean',module)
 if rc['exit_status']:sys.exit(rc['exit_status'])
