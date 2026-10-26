"""Record required sibling checks before an assigned callback is started."""
import json,subprocess,sys,re
from pathlib import Path
n=int(sys.argv[1]);root=Path(__file__).resolve().parents[2]
branches=['codex/cx-prover-rw-20261023','codex/cx-prover-dict-20261026']
tables=['docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/README.md','docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/ENTRIES.md']
def git(*args):return subprocess.check_output(['git',*args],cwd=root,text=True)
r=dict(op=n,required_log=git('log','-1','--format=%H',*branches),branches={})
for branch,table in zip(branches,tables):
 s=git('show',f'{branch}:{table}')
 lines=[l for l in s.splitlines() if l.startswith(f'|{n}|') or f'op{n} ' in l or f'op{n}`' in l]
 r['branches'][branch]=dict(revision=git('rev-parse',branch).strip(),table=table,matches=lines)
 if branch==branches[0]:
  latest='evidence/pv-rw-step-20261026/README.md'
  try:
   extra=git('show',f'{branch}:{latest}')
   r['branches'][branch]['latest_step_table']=dict(path=latest,matches=[l for l in extra.splitlines() if re.search(r'\bop\s*'+str(n)+r'\b|\|\s*'+str(n)+r'\s*\|',l)])
  except subprocess.CalledProcessError:pass
p=root/'evidence/pv-cb-20261026'/f'op{n}-sibling-check{("-"+sys.argv[2]) if len(sys.argv)>2 else ""}.json'
assert not p.exists();p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
