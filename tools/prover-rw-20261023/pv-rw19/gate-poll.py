"""One requested ten-minute gate poll; never launches a build or touches the flag."""
from pathlib import Path
import datetime,json,subprocess,sys
root=Path(__file__).resolve().parents[3]
log=root/'evidence/pv-rw19-resume-20261026/gate-polls.jsonl'
rows=[json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
number=int(sys.argv[1])
assert 1<=number<=24 and number==len(rows)+1
# Each invocation is one normal shell wait/poll. The caller resumes proof work
# only after inspecting the returned contents, never merely because time passed.
subprocess.run(['sleep','600'],check=True)
flag=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
row={'poll':number,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flag_exists':flag.exists(),'contents':flag.read_text() if flag.exists() else None}
with log.open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps(row),flush=True)
