#!/usr/bin/env python3
import subprocess,json,re,sys
from pathlib import Path
E=Path(__file__).resolve().parent.parent
p=E/'lean';p.mkdir(exist_ok=True)
rows=[]
for a in range(int(sys.argv[1]),int(sys.argv[2])):
 for n in [f'out-{a}.log',f'time-{a}.log']:
  subprocess.run(['scp','dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'+n,str(p/n)],check=True)
 subprocess.run(['scp',f'dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-prover-commit22-20261021/lean-{a}.json',str(p)],check=True)
 x=json.loads((p/f'lean-{a}.json').read_text());out=(p/f'out-{a}.log').read_text();tm=(p/f'time-{a}.log').read_text();status=int(re.search(r'^exit=(\d+)',out,re.M)[1])
 x.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_base_revision='d9865ba52',source_identity='exact source_sha256 in this receipt; additive files committed in following stage',exit_status=status,wall_time=re.search(r'Elapsed.*: (.+)',tm)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tm)[1]),swaps=int(re.search(r'Swaps: (\d+)',tm)[1]),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S),errors=[l for l in out.splitlines() if re.search(r'(?:^|: )error(?:\(|:)',l)],accepted=status==0 and x['module']!='R1Z/ProverCommitShippedAxiomAudit.lean',diagnostic_only=x['module']=='R1Z/ProverCommitShippedAxiomAudit.lean')
 if status==0:assert all('sorryAx' not in l for l in x['axioms'])
 rows.append(x)
(p/('attempts-'+sys.argv[1]+'-'+sys.argv[2]+'.jsonl')).write_text(''.join(json.dumps(x)+'\n' for x in rows))
