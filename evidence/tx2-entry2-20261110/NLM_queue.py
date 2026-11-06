from NLM_formal import run
import sys
for a,target in zip(sys.argv[1::2],sys.argv[2::2]):
 r=run(a,'lean',target)
 if r['exit_status']:sys.exit(r['exit_status'])
