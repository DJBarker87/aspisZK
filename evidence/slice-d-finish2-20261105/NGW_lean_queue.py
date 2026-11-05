from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for i,n in [(5,'ConstructorQM'),(6,'ConstructorArrays'),(7,'Reverse'),(8,'ConstructorSuccessorCell'),(9,'ConstructorSuccessor'),(10,'ConstructorPoints')]:
 a=f'NGW_L{i:03d}'
 if (E/a/'receipt.json').exists():continue
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean','NGW_'+n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
