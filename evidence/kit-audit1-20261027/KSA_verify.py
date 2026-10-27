from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;rows=[];errors=[]
for p in sorted(E.glob('KSA_[LR][0-9][0-9][0-9]/receipt.json')):
 d=json.loads(p.read_text());a=d['attempt'];rows.append(d)
 if d['exit_status']==0:
  for ax in d.get('print_axioms',[]):
   if any(s in ax for s in ['sorryAx','native_decide','Lean.ofReduceBool']):errors.append([a,'forbidden axiom',ax])
 if d['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append([a,'limits'])
 if not json.loads((E/(a+'-reservation.json')).read_text())['allowed']:errors.append([a,'unadmitted'])
 if d['kind']=='lean':
  src=d['sources'][0];p=E/a/'sources'/src
  if hashlib.sha256(p.read_bytes()).hexdigest()!=d['source_hashes'][src]:errors.append([a,'Lean snapshot'])
  if not d['deps_fingerprint'].get('aeneas_library_objects'):errors.append([a,'Aeneas pin'])
 else:
  for n in ['KSA_native_test.rs','KSA_native.py']:
   if hashlib.sha256((E/a/'sources'/n).read_bytes()).hexdigest()!=d['source_hashes'][n]:errors.append([a,'Rust snapshot',n])
  lock=json.loads((E/a/'KSA_lock.json').read_text())
  if not lock['unchanged'] or lock['before']!='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef':errors.append([a,'lock'])
# Every current module must match a successful exact compiler input.
module_checks={};theorems=[]
for p in sorted(E.glob('KSA_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 accepted=[r['attempt'] for r in rows if r['kind']=='lean' and r['exit_status']==0 and sha in r['source_hashes'].values()]
 if not accepted:errors.append([p.name,'no accepted current source'])
 module_checks[p.name]=accepted
 # Copies retain generated declarations; explicit new theorem statements all have print commands.
 if p.stem.startswith('KSA_XRn_Join_') or p.stem=='KSA_EmittedDecoder':continue
 s=p.read_text()
 for name in re.findall(r'^theorem (\w+)',s,re.M):
  if '#print axioms '+name not in s:errors.append([p.name,name,'missing axiom audit'])
  theorems.append(dict(module=p.stem,name=name))
(E/'KSA_attempts.jsonl').write_text(''.join(json.dumps(d)+'\n' for d in rows))
out=dict(errors=errors,lean_attempts=sum(d['kind']=='lean' for d in rows),rust_attempts=sum(d['kind']=='rust' for d in rows),kani_runs=0,passed=sum(d['exit_status']==0 for d in rows),failed=[d['attempt'] for d in rows if d['exit_status']],peak_rss_kib=max(int(d['peak_rss_kib']) for d in rows),swaps=sum(int(d['swaps']) for d in rows),wall_seconds=sum(d['wall_seconds'] for d in rows),current_module_accepted_inputs=module_checks,new_explicit_theorems=theorems)
(E/'KSA_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['errors','lean_attempts','rust_attempts','failed','peak_rss_kib','swaps','wall_seconds']}));print('explicit new theorem count',len(theorems))
if errors:raise SystemExit(1)
