"""Final serial raw-axiom/coherence audits in ONE admitted capped scope."""
from pathlib import Path
import subprocess,json,hashlib,sys,shutil
B=Path(__file__).resolve().parent;D=B/'NIQ_final_audit';D.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proof=B/'NIQ_native/NIQ_ProofDriver';scanner=B/'NIQ_native/NIQ_Driver'
pins=json.loads((B/'NIQ_AUDIT_PINS.json').read_text())
assert sha(proof)==pins['proof']['sha256'],'proof binary differs from eight-fixture pin'
assert sha(scanner)==pins['scanner']['sha256'],'scanner binary changed'
assert sha(B/'NIQ_native/NFA_WALKER.c')=='c041aabaccba69e3775f0e23a03c553968a05ec89f39e86bb830731ed1ec2420','walker changed'
outputs={}
for name,command in [('raw',[str(proof),'proof0']),('scan',[str(scanner),'scan'])]:
 r=subprocess.run(command,cwd=B,capture_output=True,text=True)
 (D/(name+'.log')).write_text(r.stdout+r.stderr);print(r.stdout,end='',flush=True);print(r.stderr,end='',file=sys.stderr,flush=True)
 outputs[name]=dict(command=command,exit=r.returncode,stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest())
 if r.returncode:raise SystemExit(r.returncode)
raw=[json.loads(l[11:])for l in(D/'raw.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
roots=[v for g in json.loads((B/'NIQ_AUDIT_ROOTS.json').read_text())['groups']for v in g]
assert {r['root']for r in raw}==set(roots) and len(raw)==len(roots)
assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw)
scan=[json.loads(l)for l in(B/'NIQ_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
shutil.copy2(B/'NIQ_LOADED_scan.jsonl',D/'NIQ_LOADED_scan.jsonl')
result=dict(status='PASS',commands=outputs,roots=len(raw),modules=len(scan),standard_only=True,dangling=0,incompatible_owners=0,import_mismatches=0,proof_driver_sha256=sha(proof),scanner_sha256=sha(scanner),walker_c_sha256=sha(B/'NIQ_native/NFA_WALKER.c'),fixture_reuse='NIG fixtures receipt; same unchanged proof-driver binary',serial=True)
(D/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print('NIQ_FINAL_AUDIT '+json.dumps(result),flush=True)
