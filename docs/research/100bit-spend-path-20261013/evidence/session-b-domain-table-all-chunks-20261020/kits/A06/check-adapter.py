#!/usr/bin/env python3
import argparse, subprocess
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--table',choices=['A','B'],required=True)
p.add_argument('--chunk',type=int,choices=range(16),required=True)
p.add_argument('--adapter',type=Path,required=True)
p.add_argument('--certificate',type=Path,required=True)
a=p.parse_args()
subprocess.run(['python3','/tmp/generate-r17-table-chunk.py','--table',a.table,'--chunk',str(a.chunk),'--adapter',str(a.adapter),'--output',str(a.certificate),'--check'],check=True)
