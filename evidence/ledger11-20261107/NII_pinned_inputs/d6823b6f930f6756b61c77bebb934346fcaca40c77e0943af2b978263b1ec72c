from pathlib import Path
import json,hashlib,subprocess,time,re
B=Path(__file__).resolve().parent;out=B/'NGL_delta_audit';out.mkdir(exist_ok=False)
pin=json.loads((B/'NGL_final_audit/BINARY_PIN.json').read_text())['sha256'];binary=B/'NGL_native/NGL_ProofDriver'
assert hashlib.sha256(binary.read_bytes()).hexdigest()==pin
cfg=json.loads((B/'NGL_L068.json').read_text());mode='proof7';log=out/(mode+'.log');tim=out/(mode+'.time.log');start=time.monotonic();cmd=[str(binary),mode]
with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
s=log.read_text();stats=tim.read_text()
def metric(label):return next(l.split(':',1)[1].strip() for l in stats.splitlines() if label in l)
rows=[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')]
x=dict(target=mode,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=cfg['source_revision'],parent_attempt='NGL_L068',print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=rows,same_optimized_binary_sha256=pin)
(out/(mode+'.json')).write_text(json.dumps(x,indent=1)+'\n');assert r.returncode==0 and len(rows)==4
assert all(z['equal'] and set(z['walked_axioms'])==set(z['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for z in rows)
assert hashlib.sha256(binary.read_bytes()).hexdigest()==pin
(out/'SUMMARY.json').write_text(json.dumps({'status':'PASS','roots':4,'same_optimized_binary_sha256':pin,'fixtures':'NGL_final_audit/fixtures.json (same unchanged binary; no repeat of the unchanged 52-root audit)'},indent=1)+'\n')
print(json.dumps({'status':'PASS','new_roots':4,'exit':r.returncode,'wall_seconds':x['wall_seconds']}))
