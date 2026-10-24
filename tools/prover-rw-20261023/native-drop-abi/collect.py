"""Export owned evidence only; no executables, objects or oversized JSON."""
from pathlib import Path
import hashlib,json,shutil,re
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
E=H/'native-drop-abi'; O=E/'export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=[]
def copy(p,relative):
 q=O/relative;q.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.json' and p.stat().st_size>5_000_000:
  q=q.with_suffix('.hash-size.json');q.write_text(json.dumps(dict(source=str(p),sha256=sha(p),bytes=p.stat().st_size))+'\n')
 else:shutil.copy2(p,q)
 manifest.append(dict(path=str(q.relative_to(O)),sha256=sha(q),bytes=q.stat().st_size))
for a in range(13,16):
 d=E/f'backend/ProverRwNativeDropABI-build-{a:03d}'
 for p in sorted(d.rglob('*')):
  if p.is_file() and p.suffix in ['.json','.log','.txt']:copy(p,Path('backend')/d.name/p.relative_to(d))
for a in range(36,45):
 d=E/f'extraction{a:03d}'
 for p in sorted(d.rglob('*')):
  if p.is_file() and p.suffix in ['.json','.log','.txt','.llbc','.lean']:
   rel=Path(d.name)/p.relative_to(d)
   if p.suffix=='.lean':rel=Path(str(rel)+'.txt')
   copy(p,rel)
for a in range(11570,11576):
 for p in sorted((E/'lean').glob(f'*{a}*')):
  if p.is_file():copy(p,Path('lean')/p.name)
 for p in sorted((H/'native-drop/lean').glob(f'{a}-admission-*.json')):
  copy(p,Path('lean')/p.name)
for name in ['base-provenance.json','dependency-manifest.json']:
 copy(E/'backend'/name,Path('backend')/name)
copy(E/'adaptation.json',Path('adaptation.json'))
copy(E/'ProverRwNativeDropABIPrinter.llbc',Path('inputs/ProverRwNativeDropABIPrinter-v2.llbc'))
probe=H/'src/tools/prover-rw-20261023/native-drop-abi/printer-probe'
if (probe/'Cargo.lock').exists():copy(probe/'Cargo.lock',Path('inputs/printer-Cargo.lock'))
base=E/'backend/base/src'
paths=[base/'Config.ml',base/'Main.ml',base/'interp/InterpPaths.ml',base/'interp/InterpExpressions.ml',
 H/'src/tools/prover-rw-20261023/native-entropy/reservation.py',H/'src/tools/prover-rw-20261023/native-entropy/docker_gate.py',H/'src/tools/prover-rw-20261023/native-entropy/barrier.py',
 H/'src/tools/prover-rw-20261023/native-drop/run-joint.sh',H/'src/tools/prover-rw-20261023/native-drop-abi/scope.py',
 Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py'),Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'),
 Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend/Aeneas/Std/Core/Core.lean')]
T=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
paths += [T/'lib/rustlib/src/rust/library/core/src/mem/mod.rs',T/'lib/rustlib/src/rust/library/core/src/option.rs',T/'bin/rustc',T/'bin/cargo']
assessment=dict(scope='Post-run source/dependency assessment, not a fresh ELF identity gate or historical resource repair',files=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in paths])
old=json.loads((H/'native-drop/backend/prover-rw-native-drop-build-012/receipt.json').read_text())['candidate_source_sha256']
assessment['candidate_changes_from012']={str(a):[k for k,v in json.loads((E/f'backend/ProverRwNativeDropABI-build-{a:03d}/receipt.json').read_text())['candidate_source_sha256'].items() if old.get(k)!=v] for a in range(13,16)}
assessment['copy_warning']='Private cache copy could not read old root-owned _build/.lock; remaining cache copied. No compiler launched before scoped build013; no existing cache lock was modified.'
assessment['printer_v1_input']='Receipt039 retains exact LLBC hash and Rust v1 is retained locally; original v1 LLBC bytes were overwritten by new Charon040 and are unavailable. Failure logs retained. V2 LLBC bytes are retained.'
(O/'source-assessment.json').write_text(json.dumps(assessment,indent=2)+'\n')
(O/'integrity.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(files=len(manifest),output=str(O))))
