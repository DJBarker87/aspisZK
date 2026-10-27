"""Measure independent roots sequentially; stop on admission hold, not source refusal."""
from pathlib import Path
import subprocess,sys,json
from run import H
for op,suffix in [(121,'03'),(224,'02'),(226,'02'),(227,'02')]:
 r=subprocess.run(['python3',str(H/'extract_copies.py'),str(op),suffix])
 if r.returncode==78:sys.exit(78)
 print(json.dumps(dict(op=op,suffix=suffix,exit=r.returncode)),flush=True)
