from pathlib import Path
import json,hashlib,subprocess,re
b=Path(__file__).resolve().parent
root=b/'NEA_target/kani/x86_64-unknown-linux-gnu/debug/deps'
metas=[]
for p in root.glob('aspis_r1_cost_probe*.kani-metadata.json'):
 x=json.loads(p.read_text())
 if any(h['pretty_name']=='fast_domain::NEA_line::line' for h in x['proof_harnesses']):metas.append(p)
p=max(metas,key=lambda p:p.stat().st_mtime)
x=json.loads(p.read_text());h=next(h for h in x['proof_harnesses'] if h['pretty_name']=='fast_domain::NEA_line::line')
f=Path(h['goto_file']);paths=[f,f.with_name(f.name.replace('.symtab.out','.out'))]
print(json.dumps(dict(metadata=str(p),harness=h),indent=2))
for i,f in enumerate(paths):
 if not f.exists():continue
 print('BINARY',json.dumps(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size)))
 r=subprocess.run(['/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument','--show-goto-functions',str(f)],capture_output=True,text=True)
 assert r.returncode==0,r.stderr
 (b/f'NEA_K023-goto-{i}.txt').write_text(r.stdout)
 lines=r.stdout.splitlines()
 print('HEAD\n'+'\n'.join(lines[:50]))
 hits=[i for i,l in enumerate(lines) if any(s in l for s in ['m_mul','M31::mul','line_node','line_post'])]
 print('HITS',len(hits))
 for j in hits[:80]:print('\n'.join(lines[max(0,j-2):j+4]))
