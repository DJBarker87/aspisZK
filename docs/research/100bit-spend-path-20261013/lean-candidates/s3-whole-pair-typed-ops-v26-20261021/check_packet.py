from pathlib import Path
import hashlib,json,re,sys
W=Path(__file__).resolve().parent; M=json.loads((W/'manifest.json').read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
errs=[]
for x in M['files']:
 p=W/x['path']
 if not p.is_file(): errs.append('missing '+x['path']); continue
 if p.stat().st_size!=x['bytes'] or sha(p)!=x['sha256']:errs.append('hash/size '+x['path'])
r=json.loads((W/'evidence/receipt.json').read_text())
if len(r.get('modules',[]))!=2: errs.append('expected two compiled modules')
for x in r.get('modules',[]):
 if x.get('exit_status')!=0: errs.append('failed '+str(x.get('command')))
 if x.get('lean_binary_sha256')!=M['lean']['binary_sha256']: errs.append('compiler mismatch')
 if x.get('git_head_before_popen')!=M['source_revision_before_launch']: errs.append('launch revision mismatch')
external=(W/'sources/AspisR1WeightsPairCut/FunsExternal.lean').read_text(); funs=(W/'sources/AspisR1WeightsPairCut/Funs.lean').read_text()
if re.search(r'(?m)^axiom fast_pairing\.EbyKDot\.(new|push|finish)',external): errs.append('EbyK template axiom remains')
if 'import AspisR1WeightsPairCutEbyKDotOpsV1' not in external: errs.append('typed Ops import missing')
if 'variable [fast_pairing.EbyKDotOps]' not in funs: errs.append('Funs Ops binder missing')
for p in W.rglob('*'):
 if p.is_file() and p.suffix in {'.olean','.ilean','.ir','.exe','.o','.a'}:errs.append('binary/object '+str(p.relative_to(W)))
if errs: print('\n'.join(errs));sys.exit(1)
print(f"PASS {M['schema']}: {len(M['files'])} files; full Funs and EbyK typed boundary source hashes/receipts verified")
