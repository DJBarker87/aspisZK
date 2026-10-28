from pathlib import Path
import json,hashlib,re,collections
E=Path(__file__).resolve().parent
rows=[];counts=collections.Counter();failures=[]
for p in sorted(E.glob('NBY_[KL][0-9][0-9][0-9]/receipt.json')):
 j=json.loads(p.read_text());a=j['attempt'];out=(p.parent/'stdout.log').read_text();kind=j['kind']
 assert j['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert int(j['swaps'])==0,a
 assert json.loads((E/(a+'-reservation.json')).read_text())['allowed'] is True,a
 for n,v in j['source_hashes'].items():assert hashlib.sha256((p.parent/'sources'/n).read_bytes()).hexdigest()==v,(a,n)
 if kind=='lean':
  assert '-M7000' in j['command'];assert j['exit_status']==0,(a,out)
  for s in j['print_axioms']:
   tail=s.split('depends on axioms: [')
   if len(tail)>1:assert set(tail[1].rstrip(']').split(', '))<={'propext','Classical.choice','Quot.sound'},(a,s)
  status='standard-axioms-pass'
 else:
  assert j['env']['CARGO_NET_OFFLINE']=='true' and j['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
  graph=json.loads((E/(a+'-graph.json')).read_text());assert graph['allowed'] and graph['unchanged'] and not graph['new_packages'] and not graph['edge_errors'],a
  assert graph['lock_before']==graph['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  assert j['source_hashes']['NBY_KMX_copy_stubs.patch']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
  timed='cbmc timed out' in out.lower() or 'harness timed out' in out.lower() or j['exit_status'] in [124,137]
  cfg=json.loads((E/(a+'.json')).read_text())
  if timed:status='timeout'
  elif j['exit_status']==0:
   assert not cfg.get('expected_negative'),a
   nexta=f'NBY_K{int(a[-3:])+1:03}'
   cp=E/nexta/'stdout.log'
   paired=cp.is_file() and 'VERIFICATION:- FAILED' in cp.read_text() and 'cbmc timed out' not in cp.read_text().lower()
   status='diagnostic-loop-pass' if a in ['NBY_K009','NBY_K011'] else 'paired-pass' if paired else 'pass-control-open'
  else:
   fs=re.findall(r'- Status: FAILURE\s+\t - Description: "([^"]*)"',out)
   if cfg.get('expected_negative') and len(fs)==1 and fs[0].startswith('assertion failed: !'):
    status='expected-negative-fail'
   else:
    status='finding-or-input-error';failures.append({'attempt':a,'failure_descriptions':fs})
 counts[status]+=1;rows.append({'attempt':a,'kind':kind,'status':status,'exit':j['exit_status'],'wall_seconds':j['wall_seconds'],'peak_rss_kib':int(j['peak_rss_kib']),'swaps':int(j['swaps'])})
ks=[x for x in rows if x['kind']=='kani'];ls=[x for x in rows if x['kind']=='lean'];assert len(ks)<=80 and len(ls)<=60
ledger=[json.loads(l)['attempt'] for l in (E/'NBY_ATTEMPTS.jsonl').read_text().splitlines()];assert len(ledger)==len(set(ledger))==len(rows)
out={'counts':dict(counts),'kani_used':len(ks),'kani_budget':80,'lean_used':len(ls),'lean_budget':60,'total_wall_seconds':sum(x['wall_seconds'] for x in rows),'maximum_peak_rss_kib':max(x['peak_rss_kib'] for x in rows),'swaps':sum(x['swaps'] for x in rows),'findings_or_input_errors':failures,'attempts':rows}
(E/'NBY_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='attempts'}));assert not failures,failures
