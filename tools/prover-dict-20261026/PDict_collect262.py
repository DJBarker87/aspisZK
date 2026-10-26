"""Collect exact focused Lean receipts, including rejected diagnostics."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
r=Path(__file__).resolve().parents[2]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/formatter262'
h='/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/formatter262'
t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for a in map(int,sys.argv[1:]):
 d=e/str(a);d.mkdir(exist_ok=True)
 paths={f'{a}-input.json':f'{h}/{a}-input.json',f'{a}.lean.txt':f'{h}/{a}.lean.txt',f'launch{a}.log':f'{h}/launch{a}.log',f'out-{a}.log':f'{t}/out-{a}.log',f'time-{a}.log':f'{t}/time-{a}.log',f'sha-{a}.txt':f'{t}/sha-{a}.txt'}
 for name,path in paths.items():
  subprocess.run(['scp','-q','dombarker@100.108.41.90:'+path,str(d/name)],check=True)
 x=json.loads((d/f'{a}-input.json').read_text());log=(d/f'out-{a}.log').read_text();tim=(d/f'time-{a}.log').read_text()
 assert hashlib.sha256((d/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
 reports=re.findall(r"'([^'\n]+)' (depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 x.update(exit_status=int(re.search(r'^exit=(\d+)',log,re.M)[1]),wall=re.search(r'Elapsed \(wall clock\) time.*?: (.*)',tim)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim)[1]),swaps=int(re.search(r'Swaps: (\d+)',tim)[1]),print_axioms=[dict(name=n,axioms=re.findall(r'[\w.]+',s.split('[',1)[1][:-1]) if '[' in s else [],report=s) for n,s in reports],errors=[z for z in log.splitlines() if 'error:' in z],qualification='Focused cached axiom audit or proof, not a full frozen manifest replay.')
 (d/'receipt.json').write_text(json.dumps(x,indent=2)+'\n')
 print(a,x['exit_status'],x['wall'],x['peak_rss_kib'],'reports',len(reports),'errors',len(x['errors']))
