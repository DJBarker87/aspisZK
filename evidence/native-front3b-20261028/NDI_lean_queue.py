from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
jobs=[(38,'NDI_ReaderByteRef/Types'),(39,'NDI_ReaderByteRef/Funs'),(40,'NDI_ReaderByteValue'),(41,'NDI_ReaderDomains'),(42,'NDI_ReaderByteBridge'),(43,'NDI_BatchRef/Types'),(44,'NDI_BatchRef/Funs'),(45,'NDI_BatchWord')]
for i,t in jobs:subprocess.run(['python3',str(E/'NDI_run.py'),f'NDI_L{i:03}','lean',t],check=True)
