from pathlib import Path
import subprocess,sys
b=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-20261016')
targets=[('original','PublicPreparationDiscriminantAudit'),
 ('adapted','AspisR1PublicPreparation.Types'),('adapted','PublicPreparationDiscriminantAudit'),
 ('adapted','AspisR1PublicPreparation.Funs'),('adapted','PublicPreparationActualAudit'),
 ('adapted','ExtractedPublicPreparationSuccess'),('adapted','PreparationSerializerJoint')]
for mode,target in targets:
 w=b/('proofs-naming-'+mode)
 command=['python3',str(w/'runner.py'),'run',str(w),'--target',target,
  '--external-snapshot',str(w/'external-inputs.json'),'--attempt','naming-a',
  '--revision','9cf712b0504622c2068ac5948a6244db15071552 plus names-only overlay']
 code=subprocess.run(command).returncode
 if code:sys.exit(code)
