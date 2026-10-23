from pathlib import Path
import hashlib,json,subprocess
H=Path(__file__).resolve().parent
base=json.loads((H/'S2F-base-pins.json').read_text())
def pin(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
checked=[]
for v in base['tools']+[x for rows in base['reference_dependency_sources'].values() for x in rows]:
 got=pin(v['path']);assert got['sha256']==v['sha256'],v['path'];checked.append(got)
objects={}
for p in sorted(H.glob('S2F_*.olean')):objects[p.stem]=pin(p)
objects.update({m:v['selected'] for m,v in base['objects'].items()})
for v in objects.values():assert pin(v['path'])['sha256']==v['sha256']
artifacts=[]
for p in sorted((H/'kani-target').rglob('s2f_steps*')):
 if p.is_file() and p.suffix in ['.out','.json']:
  artifacts.append(pin(p))
extra=[]
for p in [H/'S2F_cc',H/'S2F_run_host.py',H/'S2F_reservation.py',H/'S2F-steps/Cargo.lock',Path('/home/dombarker/.cargo/bin/cargo-kani').resolve(),Path('/home/dombarker/.cargo/bin/cargo').resolve(),Path('/home/dombarker/project-offloads/codex-cx-s2e-20261023/S2E-reference/src/S2E_Reference.rs')]:
 extra.append(pin(p))
(H/'S2F-host-pins.json').write_text(json.dumps(dict(checked_inherited_tools_and_dependency_sources=checked,objects=objects,goto_artifact_candidates=artifacts,extra=extra,qualification='Read-only final fingerprint of private objects, reused tools/dependencies and all retained GOTO candidates. Artifact candidates are not assigned historical target identities; per-attempt compiled sources/commands and property logs give focused evidence. This is not a coherent frozen release rebuild.'),indent=2)+'\n')
state=subprocess.check_output(['ps','-u','dombarker','-o','pid,ppid,rss,args'],text=True)
(H/'S2F-final-host-state.txt').write_text('\n'.join(l for l in state.splitlines() if 'codex-cx-s2f-20261023' in l or 'S2F_' in l)+'\n')
print(json.dumps(dict(checked_inherited=len(checked),objects=len(objects),goto_artifact_candidates=len(artifacts),extra=len(extra))))
