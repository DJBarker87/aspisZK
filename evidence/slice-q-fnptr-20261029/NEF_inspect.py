from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
files=[p for p in (B/'NEF_target').rglob('*') if p.is_file() and (p.suffix in ['.out','.json'] or p.name.endswith('.symtab'))]
print(json.dumps([dict(path=str(p.relative_to(B)),bytes=p.stat().st_size) for p in files]))
for p in files:
 if p.suffix!='.out' or p.name.endswith('.symtab.out'):continue
 r=subprocess.run(['/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument','--show-goto-functions',str(p)],capture_output=True,text=True)
 if r.returncode:continue
 chunks=r.stdout.split('\n\n')
 kept=[s for s in chunks if any(n in s for n in ['NBZ_mark_none','NBZ_return_carriers','Option::<fn','option..Option','is_none','is_some'])]
 out='\n\n'.join(kept);(B/('NEF_GOTO_'+p.name+'.txt')).write_text(out)
 print(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),exit=r.returncode,full_bytes=len(r.stdout),kept=out)))
