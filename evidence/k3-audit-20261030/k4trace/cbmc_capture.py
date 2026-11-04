#!/usr/bin/python3
"""Transparent stdout tee of the original pinned CBMC; no flag/result rewriting."""
from pathlib import Path
import subprocess,os,sys,json,hashlib
out=Path(os.environ['K4TRACE_OUT']);stem='cbmc-'+str(os.getpid())
real='/home/dombarker/.kani/kani-0.67.0/bin/cbmc'
(out/(stem+'-command.json')).write_text(json.dumps({'executable':real,'sha256':hashlib.file_digest(open(real,'rb'),'sha256').hexdigest(),'argv':sys.argv[1:]},indent=2)+'\n')
p=subprocess.Popen([real,*sys.argv[1:]],stdout=subprocess.PIPE)
with (out/(stem+'.json')).open('wb')as f:
 while b:=p.stdout.read(65536):
  f.write(b);f.flush();sys.stdout.buffer.write(b);sys.stdout.buffer.flush()
sys.exit(p.wait())
