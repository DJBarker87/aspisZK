"""Serial Python-only reproduction and receipts. Never launches a build scope."""
from pathlib import Path
import subprocess,hashlib,json,time,os,re
E=Path(__file__).resolve().parent;R=E.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
def run(a,script,seed='1'):
 cmd=['/usr/bin/time','-l','python3',str(E/script)];env=dict(os.environ,PYTHONHASHSEED=seed,PYTHONDONTWRITEBYTECODE='1')
 start=time.monotonic();p=subprocess.run(cmd,cwd=R,env=env,capture_output=True,text=True);wall=time.monotonic()-start
 (E/(a+'.stdout.log')).write_text(p.stdout);(E/(a+'.time.log')).write_text(p.stderr)
 m=re.search(r'(\d+)\s+maximum resident set size',p.stderr);sw=re.search(r'(\d+)\s+swaps',p.stderr)
 receipt=dict(attempt=a,target=script,command=cmd,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_tree_dirty=True,script_sha256=sha((E/script).read_bytes()),dependencies={p.name:sha(p.read_bytes()) for p in E.glob('NKS_*.py')},python_hash_seed=seed,exit_status=p.returncode,wall_seconds=wall,peak_rss_kib=int(m[1])//1024 if m else None,swaps=int(sw[1]) if sw else None,swap_note='macOS time -l reports swaps if available; null means unreported, not zero',print_axioms='N/A: no Lean theorem or compile; inventory only',kind='PYTHON_READ_ONLY_CENSUS_OR_VALIDATION',host_scope=False,stdout=a+'.stdout.log',resource_log=a+'.time.log')
 (E/(a+'.json')).write_text(json.dumps(receipt,indent=1,sort_keys=True)+'\n')
 with (E/'NKS_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt,sort_keys=True)+'\n')
 assert p.returncode==0,a+' failed; inspect retained logs'
 return receipt
names=['NKS_INVENTORY.json','NKS_ROOTS.json','NKS_GRAPH.json.xz','NKS_GRAPH.json.sha256','NKS_SOURCE_AST.json.xz','NKS_SOURCE_AST.json.sha256']
run('NKS_P001','NKS_inventory.py','1');one={n:sha((E/n).read_bytes()) for n in names}
run('NKS_P002','NKS_inventory.py','9173');two={n:sha((E/n).read_bytes()) for n in names};assert one==two
(E/'NKS_DETERMINISM.json').write_text(json.dumps(dict(status='IDENTICAL',runs=['NKS_P001','NKS_P002'],hash_seeds=['1','9173'],first=one,second=two,method='Two independent parser/MIR/mono/overlay/closure generations from the same pinned inputs; no compiler replay.',build_scopes_used=0),sort_keys=True,indent=1)+'\n')
run('NKS_P003','NKS_report.py');run('NKS_P004','NKS_validate.py')
print('NKS deterministic census and assessment complete; all four Python receipts pass, no build/prover scope.')
