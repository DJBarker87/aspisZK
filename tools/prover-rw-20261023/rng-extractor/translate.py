"""Invoke only the job-owned candidate, with exact binary/input pins."""
from pathlib import Path
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parent
kind=sys.argv[1]
assert kind in ['synthetic','selected64']
B=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/base/src/_build/default/main.exe')
inp=D/('ProverRwRngExtractor'+kind+'.llbc')
dest=D/(kind+'-generated')
dest.mkdir(exist_ok=False)
cmd=[str(B),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
    '-namespace','ProverRwRngExtractor'+kind,'-dest',str(dest),'-split-files','-emit-json',str(inp)]
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
(dest/'candidate-input-pins.json').write_text(json.dumps(dict(command=cmd,binary=pin(B),input=pin(inp),
    drop_as_no_op=False,source_association='Experimental candidate; no native provider installation or operation-simulation proof'),indent=2)+'\n')
raise SystemExit(subprocess.run(cmd).returncode)
