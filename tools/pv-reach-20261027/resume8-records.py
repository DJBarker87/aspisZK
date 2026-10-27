"""Collect committed Stream B compile evidence without accessing sibling worktrees."""
import json,subprocess,pathlib,re
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume8';want={r['module'] for r in json.loads((E/'prerequisites-before.json').read_text())};out=[]
for branch,prefix in [('codex/pv-cb-20261026','evidence/pv-cb-20261026'),('codex/pv-join-20261026','evidence/pv-join-20261026')]:
 paths=subprocess.check_output(['git','ls-tree','-r','--name-only',branch,prefix],text=True).splitlines()
 paths=[p for p in paths if re.search(r'/(?:[0-9]+|[0-9]+-receipt|receipt-[0-9]+)\.json$',p)]
 for p in paths:
  d=json.loads(subprocess.check_output(['git','show',branch+':'+p]))
  if not isinstance(d,dict):continue
  m=d.get('module',d.get('target','')).replace('/','.')
  if m not in want:continue
  if d.get('exit',d.get('exit_status'))!=0:continue
  out.append(dict(branch=branch,evidence_path=p,**d))
(E/'stream-b-build-records.json').write_text(json.dumps(out,indent=2)+'\n');print('successful build records',len(out),'modules',len({d.get('module',d.get('target','')).replace('/','.') for d in out}))
