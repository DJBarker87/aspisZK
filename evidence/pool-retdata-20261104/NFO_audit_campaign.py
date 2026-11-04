from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parent
steps=[(35,'NFO_WALKER','lean'),(36,'NFO_MemoryLimit','lean'),(37,'NFO_Driver','lean'),(38,'NFO_Driver','link'),(39,'NFO_Driver','fixtures'),(40,'NFO_Driver','final'),(41,'NFO_Coherence','lean'),(42,'NFO_Coherence','scan-link'),(43,'NFO_Coherence','scan')]
for i,target,mode in steps:
 r=subprocess.run([sys.executable,str(p/'NFO_run.py'),f'NFO_L{i:03}',target,mode])
 if r.returncode:sys.exit(r.returncode)
