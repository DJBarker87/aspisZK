from pathlib import Path
import subprocess,sys
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-20261016/proofs-naming-adapted')
targets=[('PublicPreparationDiscriminantAudit','tags-a'),
 ('AspisR1PublicPreparation.Funs','funs-a'),('PublicPreparationActualAudit','actual-a'),
 ('ExtractedPublicPreparationSuccess','success-a'),('PreparationSerializerJoint','joint-a')]
for target,attempt in targets:
 command=['python3',str(w/'runner.py'),'run',str(w),'--target',target,
  '--external-snapshot',str(w/'external-inputs.json'),'--attempt',attempt,
  '--revision','9cf712b0504622c2068ac5948a6244db15071552 plus names-only overlay']
 code=subprocess.run(command).returncode
 if code:sys.exit(code)
