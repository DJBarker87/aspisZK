"""Read-only whole assigned-block audit, including ID-bearing receipt directories."""
from pathlib import Path
import re,json
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');B=D.parent;hits=[]
pattern=re.compile(r'(?<![0-9a-fA-F])(414[0-9][0-9])(?![0-9a-fA-F])')
for d in B.glob('codex-pv-*'):
 if d==D:continue
 for p in d.glob('**/*414[0-9][0-9]*'):
  m=pattern.search(p.name)
  if m:hits.append(dict(id=int(m[1]),path=str(p),directory=p.is_dir()))
sent=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/evidence/sent.txt').read_text();shared=[]
for line in sent.splitlines():
 x=line.split()
 if len(x)>=3 and x[2].isdigit() and 41400<=int(x[2])<=41499:shared.append(line)
record=dict(block=[41400,41499],other_job_id_paths=hits,shared_sent=shared,own_launched=[int(p.name[5:]) for p in D.glob('lean-*') if (p/'time.log').exists() and 'Exit status:' in (p/'time.log').read_text()],rule='Both receipt directories and files checked; hexadecimal substrings excluded. Read-only audit; any earlier collision is reported, never rerun.')
(D/'resume-id-audit.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
