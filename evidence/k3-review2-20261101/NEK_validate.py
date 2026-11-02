"""Strict receipt/source/budget audit; incomplete checks earn no credit."""
from NEK_scan import *
from NEK_verdict import verdict
import ast
from NEK_host import B

def main():
 attempts=[json.loads(l) for l in (E/'NEK_ATTEMPTS.jsonl').read_text().splitlines()];ids=[r['attempt'] for r in attempts];assert len(ids)==len(set(ids))
 counts=collections.Counter(r['kind'] for r in attempts);assert counts['kani']<=240 and counts['lean']<=10
 blobs={}
 for p in E.glob('*.json.xz'):
  if any(s in p.name for s in ['IMMUTABLE','FIDELITY']):
   try:v=read_json(p)
   except Exception:continue
   if isinstance(v,dict) and any(k.startswith(('crates/','programs/')) for k in v):blobs[sha(p.read_bytes())]=(p,v)
 transport=[json.loads(l) for l in (E/'NEK_NATIVE_TRANSPORT.jsonl').read_text().splitlines()]
 tree=ast.parse((E/'NEK_host.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='admit');call=next(n for n in ast.walk(fn) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='py')
 admission_expr=compile(ast.Expression(call.args[0]),'<own admission template>','eval')
 rows=[]
 for r in attempts:
  a=r['attempt'];ad=read_json(E/(a+'-reservation.json'));assert ad.get('allowed') is True,a
  admission_code=eval(admission_expr,{'B':B,'a':a,'retry':r['reservation_retries']});sig=sha(admission_code.encode());assert any(t['input_sha256']==sig and t['exit']==0 for t in transport if t.get('input_sha256')),('admission exit0 absent',a)
  disk=read_json(E/a/'receipt.json');assert disk==r,a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert int(r['swaps'])==0 and r['source_revision'] and r['module']
  log=(E/a/'stdout.log').read_text();row=dict(attempt=a,kind=r['kind'],exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib'],swap=r['swaps'],source_revision=r['source_revision'],admission='allowed true AND exit 0, exact request code hash')
  if r['kind']=='lean':
   if r['exit_status']!=0:
    row.update(verdict='OPEN',incomplete_reason='Lean compilation failed; printed sorryAx during error is rejected and earns no credit');rows.append(row);continue
   axioms=[l for l in log.splitlines() if 'depends on axioms:' in l or 'does not depend on any axioms' in l];assert len(axioms)==len(r['print_axioms'])
   for line in axioms:
    names=line.split('[',1)[1].split(']',1)[0].replace(' ','').split(',') if '[' in line else [];assert set(names)<={'propext','Quot.sound','Classical.choice'}
   row['axioms']=axioms;rows.append(row);continue
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  ni=r['native_command'];assert '--locked' not in ni and '--features' in ni
  g=read_json(E/(a+'-graph-check.json'));assert g['exact_frozen_selected_graph'] and g['graph_matches_frozen'] and g['resolved_features_all_crates'],a
  s=read_json(E/(a+'-source-check.json'));assert not s['errors'],a
  lock=E/(a+'-lock-check.json')
  if lock.exists():assert read_json(lock)['unchanged'],a;row['post_lock']='unchanged'
  else:
   row['post_lock']='native postcheck incomplete; requires read-only recovery; no credit'
   assert verdict(log)=='OPEN',a
  dep=r.get('deps_fingerprint',{});bundle=dep.get('fidelity_bundle_sha256') or dep.get('immutable_bundle_sha256')
  expected=None
  overlay=E/(a+'_overlay.json')
  if bundle:assert bundle in blobs,(a,bundle);expected=blobs[bundle][1]
  elif overlay.exists():expected=read_json(overlay)
  if expected:
   for n,t in expected.items():assert r['source_hashes'].get('NEK_src/'+n)==sha(t.encode()),(a,n,'source/bundle mismatch')
   for n,t in expected.items():
    assert not re.search(r'\bstatic\s+mut\b',t),(a,n)
    assert not re.search(r'\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',t),(a,n)
  row.update(verdict=verdict(log),source_bundle_checked=bool(expected),graph='exact frozen selected packages/edges and all resolved features',axioms='N/A: Kani')
  if 'could not compile' in log:row['incomplete_reason']='compile error'
  elif verdict(log)=='OPEN':row['incomplete_reason']='timeout/unwind/other incomplete check'
  rows.append(row)
 out=dict(kani_used=counts['kani'],kani_limit=240,lean_used=counts['lean'],lean_limit=10,rows=rows,validation='PASS',scope='receipt integrity/resource/source/graph audit; no automatic semantic or composition adoption')
 (E/'NEK_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
if __name__=='__main__':main()
