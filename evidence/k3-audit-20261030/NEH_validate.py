from NEH_scan import *
errors=[];done=[]
for q in sorted(E.glob('NEH_K*/receipt.json')):
 r=read_json(q);a=r['attempt'];num=int(a.removeprefix('NEH_K'));log=(q.parent/'stdout.log').read_text();v='OPEN' if 'timed out' in log.lower() else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'FAIL' if 'VERIFICATION:- FAILED' in log else 'OPEN'
 if r.get('limits')!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+':limits')
 if str(r['swaps'])!='0':errors.append(a+':swaps')
 g=E/(a+'-graph-check.json');l=E/(a+'-lock-check.json')
 if v in ['PASS','FAIL']:
  if not g.exists() or not read_json(g).get('exact_frozen_selected_graph'):errors.append(a+':graph')
  if not l.exists() or not read_json(l).get('unchanged'):errors.append(a+':lock')
  if r['env'].get('CARGO_NET_OFFLINE')!='true':errors.append(a+':offline')
  if r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3':errors.append(a+':optimization')
 source=E/(a+'_sources.json.xz')
 if source.exists():
  for n,t in read_json(source).items():
   if r['source_hashes'].get('NEH_src/'+n)!=sha(t.encode()):errors.append(a+':source:'+n)
 else:
  source=E/(a+'.rs')
  if source.exists():
   hs=[h for n,h in r['source_hashes'].items() if n.endswith('/NBZ_native.rs')]
   if hs != [sha(source.read_bytes())]:errors.append(a+':diagnostic-source')
 done.append(dict(attempt=a,verdict=v,exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision']))
assert len(done)<=120
# Source freeze assessment is a comparison, not a new ELF rebuild.
changed=subprocess.check_output(['git','diff','--name-only',FROZEN,'--','crates','programs'],text=True).splitlines()
# Sparse checkout may omit paths, but git's tracked comparison still checks source.
result=dict(status='PASS' if not errors else 'FAIL',attempts=len(done),errors=errors,receipts=done,changed_shipped_paths=changed,print_axioms='N/A: no new Lean theorem',scope='receipt consistency and resource/graph/source checks, not a new prover regression')
(E/'NEH_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','attempts','errors','changed_shipped_paths']}));assert not errors
