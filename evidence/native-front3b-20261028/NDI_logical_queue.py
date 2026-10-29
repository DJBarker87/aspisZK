from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for i,target in [(50,'NDI_BatchRun'),(51,'NDI_BatchBridge'),(52,'NDI_BatchControl'),(53,'NDI_PredicatesRef/Types'),(54,'NDI_PredicatesRef/Funs'),(55,'NDI_PredicatesBridge'),(56,'NDI_IteratorFrame')]:
 subprocess.run(['python3',str(E/'NDI_run.py'),f'NDI_L{i:03}','lean',target],check=True)
