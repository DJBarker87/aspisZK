from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for i,t in [(58,'NDI_BatchRun'),(59,'NDI_BatchBridge'),(60,'NDI_PredicatesBridge'),(61,'NDI_IteratorFrame'),(62,'NDI_PredicateLoops'),(63,'NDI_ParseShapeTail')]:
 subprocess.run(['python3',str(E/'NDI_run.py'),f'NDI_L{i:03}','lean',t],check=True)
