#!/usr/bin/env python3
"""Read-only receipt/source audit, no compiler or prover invocation."""
from pathlib import Path
import hashlib,json,subprocess,time,tomllib,re
start=time.monotonic();root=Path(__file__).resolve().parents[2];base=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];freeze=json.loads((base/'PoolW_FREEZE.json').read_text())
for name,pin in freeze['files'].items():
 p=root/name
 if sha(p)!=pin['sha256'] or p.stat().st_size!=pin['bytes']:errors.append('freeze '+name)
inputs=json.loads((base/'PoolW_INPUTS.json').read_text())
for pin in inputs['inputs']:
 if sha(root/pin['path'])!=pin['sha256']:errors.append('release input '+pin['path'])
host=json.loads((base/'PoolW_HOST_INPUT_MATCH.json').read_text())
if host['errors']:errors.extend(host['errors'])
if len(host['inputs'])!=len(inputs['inputs']):errors.append('host source count')
for manifest,location in [('PoolW_SLICES.json','PoolW_guard/PoolW_lib.rs'),('PoolW_CPISLICES.json','PoolW_cpi/PoolW_lib.rs')]:
 proof=(base/location).read_text()
 for row in json.loads((base/manifest).read_text()):
  frag=''.join((root/row['file']).read_text().splitlines(keepends=True)[row['first']-1:row['last']])
  if hashlib.sha256(frag.encode()).hexdigest()!=row['sha256'] or frag not in proof:errors.append('slice '+str(row))
records=[]
for receipt in sorted(base.glob('PoolW_*/receipt.json')):
 x=json.loads(receipt.read_text());kind=x['kind'];attempt=x['attempt'];out=receipt.parent
 for name,h in x['source_hashes'].items():
  if sha(out/'sources'/name)!=h:errors.append('snapshot '+attempt+' '+name)
 if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('caps '+attempt)
 if x['swaps']!='0':errors.append('swap '+attempt)
 if kind=='lean' and x['exit_status']==0:
  for line in x['print_axioms']:
   match=re.search(r'depends on axioms: \[([^]]*)\]',line)
   if match and set(match[1].split(', '))-{'propext','Classical.choice','Quot.sound'}:errors.append('axioms '+attempt)
 if kind=='kani' and x['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3':errors.append('optimization '+attempt)
 log=(out/'stdout.log').read_text()
 status=('pass' if x['exit_status']==0 else 'timeout' if 'timed out' in log or x['exit_status']==124 else 'unwind' if 'unwinding assertion' in log else 'compile/error')
 records.append({k:x.get(k) for k in ['attempt','kind','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}|{'classification':status,'receipt':str(receipt.relative_to(root))})
lean=[r for r in records if r['kind']=='lean'];kani=[r for r in records if r['kind']=='kani']
if len(lean)!=15:errors.append('Lean receipts '+str(len(lean)))
if len(kani)!=40:errors.append('Kani receipts '+str(len(kani)))
if {r['attempt'] for r in kani}!={f'PoolW_KANI{i:03}' for i in range(1,41)}:errors.append('Kani IDs')
for source in (root/'lean').glob('PoolW_*.lean'):
 if not any(r['exit_status']==0 and r['source_hashes'].get(source.name)==sha(source) for r in lean):errors.append('unchecked current source '+source.name)
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b',source.read_text()):errors.append('forbidden source '+source.name)
for path in subprocess.check_output(['git','diff','--name-only',freeze['revision']],cwd=root,text=True).splitlines():
 if not (path.startswith('lean/PoolW_') or path.startswith('evidence/pool-write-20261026/')):errors.append('scope '+path)
# SDK leaf versions/checksums must match the frozen dependency lock.
locked=tomllib.loads((root/'Cargo.lock').read_text())['package'];names={'solana-program','solana-account-info','solana-pubkey','solana-rent','solana-program-error','solana-sdk-ids'}
expected={p['name']:(p['version'],p.get('checksum')) for p in locked if p['name'] in names}
for crate in ['PoolW_guard','PoolW_cpi','PoolW_pure']:
 lock=tomllib.loads((base/crate/'PoolW_resolved.lock').read_text())['package']
 for p in lock:
  if p['name'] in names and (p['version'],p.get('checksum'))!=expected[p['name']]:errors.append('SDK '+crate+' '+p['name'])
for r in records:
 if r['kind']=='lean' and r['exit_status']==0 and not r['print_axioms']:errors.append('missing audit '+r['attempt'])
summary={'source_revision':freeze['revision'],'audit_revision_anchor':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'scope':'Source freeze, exact native slices, actual host/release-input identity, focused receipts, axioms and assigned diff only; not complete source-to-ELF or P1/history theorem','repository_compiler_input_union':len(inputs['inputs']),'lean_attempts':len(lean),'kani_attempts':len(kani),'lean_pass':sum(r['exit_status']==0 for r in lean),'kani_pass':sum(r['exit_status']==0 for r in kani),'kani_classification':{s:sum(r['classification']==s for r in kani) for s in ['pass','timeout','unwind','compile/error']},'inspection_wall_seconds':time.monotonic()-start,'errors':errors,'exit':int(bool(errors))}
(base/'PoolW_ATTEMPTS.json').write_text(json.dumps(records,indent=2)+'\n');(base/'PoolW_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));raise SystemExit(bool(errors))
