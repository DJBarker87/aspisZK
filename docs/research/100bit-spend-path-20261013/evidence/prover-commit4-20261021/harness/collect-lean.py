#!/usr/bin/env python3
import subprocess,json,re
from pathlib import Path
E=Path(__file__).resolve().parent.parent
p=E/'lean';p.mkdir(exist_ok=True)
rows=[]
for a in range(8144,8153):
 for n in [f'out-{a}.log',f'time-{a}.log']:
  subprocess.run(['scp','dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'+n,str(p/n)],check=True)
 subprocess.run(['scp',f'dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-prover-commit4-20261021/lean-{a}.json',str(p)],check=True)
 x=json.loads((p/f'lean-{a}.json').read_text());out=(p/f'out-{a}.log').read_text();tm=(p/f'time-{a}.log').read_text();status=int(re.search(r'^exit=(\d+)',out,re.M)[1])
 x.update(source_base_revision='b5406a5912f3eaa7bc44e21b9d3327d75d80280c',source_identity='exact source_sha256 in this receipt; additive files committed in following stage',exit_status=status,wall_time=re.search(r'Elapsed.*: (.+)',tm)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tm)[1]),swaps=int(re.search(r'Swaps: (\d+)',tm)[1]),axioms=[l for l in out.splitlines() if 'depends on axioms:' in l],errors=[l for l in out.splitlines() if 'error' in l],accepted=status==0)
 if status==0:assert all('sorryAx' not in l for l in x['axioms'])
 rows.append(x)
(p/'attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
