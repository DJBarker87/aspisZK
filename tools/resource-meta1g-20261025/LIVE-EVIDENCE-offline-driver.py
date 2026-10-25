"""Measured local offline replay; no SSH or host commands."""
import hashlib,json,os,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
OUT=HERE.parents[1]/'evidence/resource-meta1g-20261025'
argv=[sys.executable,'-B',str(HERE/'LIVE-EVIDENCE-replay.py')]
start=time.monotonic()
with (OUT/'LIVE-EVIDENCE-offline-replay.log').open('xb') as f:
    child=subprocess.Popen(argv,stdout=f,stderr=subprocess.STDOUT)
    _,status,u=os.wait4(child.pid,0);code=os.waitstatus_to_exitcode(status);child.returncode=code
receipt=dict(command=argv,exit=code,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_pins={p.name:dict(size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [HERE/'LIVE-EVIDENCE-replay.py',HERE/'LIVE-EVIDENCE-capture.py',HERE/'LIVE-EVIDENCE-offline-driver.py']},print_axioms='N/A')
with (OUT/'LIVE-EVIDENCE-offline-receipt.json').open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(json.dumps(receipt));sys.exit(code)
