from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s1-embedding-export-v1';O.mkdir(exist_ok=False);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for v in [1,2]:
 P=H/f's1-source-m31-embedding-v{v}'
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('embedding')/f'v{v}'/rel)
 copy(P/'Embedding.llbc',Path('embedding')/f'v{v}'/'Embedding.llbc.json')
 for p in (P/'generated').rglob('*'):
  if p.is_file():copy(p,Path('embedding')/f'v{v}'/'generated'/(str(p.relative_to(P/'generated'))+'.txt'))
 for phase in ['charon','aeneas']:
  tag=f's1-m31-embedding-{phase}-v{v}'
  for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
  for p in (H/'receipts'/tag).iterdir():
   if p.suffix in ['.log','.json']:copy(p,Path('receipts')/tag/p.name)
for tag in ['s1-original-claim-joinfix-v1','s1-original-claim-collapse-v1']:
 for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.log','.json']:copy(p,Path('receipts')/tag/p.name)
 for f in ['input-lib.rs','tool.patch']:copy(H/tag/f,Path('original-claim-excluded')/tag/f)
for v in [1,2,3]:
 W=H/f's1-collapse-tool-v{v}'
 for f in ['input.json','receipt.json','candidate.patch','admission-global.json','admission-app-scopes.json','build.log','time.log','container-id.txt']:
  p=W/f
  if p.exists():copy(p,Path('tool-build')/f'v{v}'/f)
 # Exact source text changed by the candidate, never the compiled binary.
 copy(W/'source/src/interp/InterpReduceCollapse.ml',Path('tool-build')/f'v{v}'/'InterpReduceCollapse.ml')
# Reuse the same dependency text, and validate every source inventory entry.
D=Path('/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core');pins=load(H/'s1-m31-embedding-charon-v2-input.json')['dependency_source_pins']
for rel,d in pins.items():assert sha(D/rel)==d;copy(D/rel,Path('dependency/aspis-core')/rel)
for name in ['run-original-claim-joinfix-host.py','run-original-claim-collapse-host.py','build-original-claim-collapse-fix-host.py','extract-s1-m31-embedding-host.py','capped.py','reservation.py']:copy(H/'kit'/name,Path('runner')/name)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',embedding_v1='Opaque entry probe only, no accepted source leaf.',embedding_v2='Actual four CodeField from_m31 implementations, inherent constructors and canonicalizer are included and emitted; Lean source/totality/query/caller proofs checked separately.',original_claim='BOTH attempts EXCLUDED. Older cached circle fix rejects nested-loop returns; isolated identity-remap tool moves Not_found to missing abstraction. No bypass or source-equivalence credit.',tool_build='v1 preflight gate failure: snapshot is not a git repository, no build launched; own gate container stopped. v2 missing GNU time: no compiler launched, exit127. v3 binds host GNU time read-only, warm one-module compile/link succeeds under verified6G/8G/Swap0/pids64. Tool is a candidate and original claim extraction still fails; no adoption claim.',remaining='S1 original nested-claim/fission equivalence and full source children/Std/caller installation and S6 actual SDK binding remain. No100-bit conclusion.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n');print(str(O))
