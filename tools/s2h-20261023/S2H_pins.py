from pathlib import Path
import hashlib,json,sys,subprocess,os
B=Path(__file__).resolve().parent;c=B/sys.argv[1];x=json.loads(c.read_text());paths=x['env']['LEAN_PATH'].split(':');seen={}
# Pin all selected cached objects by module-relative path; earlier overlays win.
for root in paths:
 p=Path(root)
 if not p.is_dir():continue
 for obj in sorted(p.rglob('*.olean')):
  key=str(obj.relative_to(p))
  if key not in seen:seen[key]={'path':str(obj),'sha256':hashlib.sha256(obj.read_bytes()).hexdigest(),'bytes':obj.stat().st_size}
(B/'lakefile.toml').write_text('name = "s2h"\nversion = "0.1.0"\n');(B/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
pin=B/(x['attempt']+'-objects.json');pin.write_text(json.dumps(seen,sort_keys=True,indent=2)+'\n')
x['deps_fingerprint']={'selected_overlay_sha256':hashlib.sha256(pin.read_bytes()).hexdigest(),'selected_object_count':len(seen),'scope':'cached focused overlay only; sysroot pins reused from S2E, not a coherent release rebuild'}
c.write_text(json.dumps(x,indent=2)+'\n');r=subprocess.run([sys.executable,str(B/'S2H_run_host.py'),sys.argv[1]])
(B/x['attempt']/'objects.json').write_bytes(pin.read_bytes());sys.exit(r.returncode)
