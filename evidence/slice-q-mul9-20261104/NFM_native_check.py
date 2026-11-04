"""Strict evidence checks for ruling(ad); model equalities alone never close rows."""
from pathlib import Path
import json,hashlib,sys
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(condition,message):
 if not condition:raise ValueError(message)
def check():
 rows={int(p.parent.name[-3:]):obj(p) for p in E.glob('NFM_K*/receipt.json')}
 require(set(rows)==set(range(1,101)),'native attempt ledger incomplete')
 groups=[]
 def group(label,positive,negatives,copy_positive,copy_negative):
  ids=[positive,*negatives,copy_positive,copy_negative];rs=[rows[i] for i in ids]
  require([r['exit_status'] for r in rs]==[0]+[1]*len(negatives)+[0,1],label+': unexpected exits')
  require(all(rows[i]['module']==rows[positive]['module'] for i in negatives),label+': renamed harness')
  for i in ids:
   log=(E/rows[i]['attempt']/'stdout.log').read_text()
   require(('VERIFICATION:- SUCCESSFUL' if i in [positive,copy_positive] else 'VERIFICATION:- FAILED') in log and 'timed out' not in log,label+': wrong verdict/timeout')
  require(len({sha(E/r['attempt']/'NFM_harness.patch') for r in rs})==1,label+': copy/control payload drift')
  groups.append(dict(label=label,positive=rows[positive]['attempt'],negative=[rows[i]['attempt'] for i in negatives],copy_positive=rows[copy_positive]['attempt'],copy_negative=rows[copy_negative]['attempt'],same_payload=True))
 group('fixed native control',1,[2],97,98)
 for cut in range(7):group(f'complete window {cut}',5+2*cut,[6+2*cut],3,4)
 for cut in range(7):group(f'rejected term {cut}',21+2*cut,[22+2*cut],19,20)
 group('wrapper832',37,[38],35,36)
 for cut in range(7):group(f'one-iteration borrowed frame {cut}',44+7*cut,list(range(45+7*cut,51+7*cut)),42,43)
 group('typed terminal WideExact add',93,[94],42,43)
 group('final fold/head frame',99,[100],95,96)
 # Check every admitted run, including excluded timeout and unused copy controls.
 tools0={p:v['sha256'] for p,v in obj(E/'NFM_K001-tool-check.json')['binaries'].items()}
 payloads={};payload_hashes={}
 for i,r in rows.items():
  payload_name=('NFM_CONTROL_PAYLOAD.json' if i in [1,2,97,98] else 'NFM_WINDOW_PAYLOAD.json' if i<=18 else 'NFM_REJECT_PAYLOAD.json' if i<=34 else 'NFM_WRAPPER_PAYLOAD.json' if i<=38 else 'NFM_STRICT_PAYLOAD.json' if i<=41 else 'NFM_SPLIT_FRAME_PAYLOAD.json' if i<=94 else 'NFM_FINAL_FRAME_PAYLOAD.json')
  if payload_name not in payload_hashes:payload_hashes[payload_name]={name:hashlib.sha256(text.encode()).hexdigest() for name,text in obj(E/payload_name).items()}
  for name,h in payload_hashes[payload_name].items():require(r['source_hashes'].get('NFM_src/'+name)==h,r['attempt']+': current payload differs from compiled source')
  require({p:v['sha256'] for p,v in obj(E/(r['attempt']+'-tool-check.json'))['binaries'].items()}==tools0,r['attempt']+': tool drift')
  a=r['attempt'];ad=obj(E/(a+'-admission.json'));require(ad['exit']==0 and ad['reservation']['allowed'] is True,a+': admission')
  require(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a+': cap drift')
  require(r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a+': optimization/offline drift')
  require(r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a+': copy patch')
  graph=obj(E/(a+'-graph-check.json'));require(graph['graph_matches_frozen'] and graph['resolved_features_all_crates'],a+': frozen graph/features')
  require(not obj(E/(a+'-rule16-check.json'))['static_declarations'],a+': static')
  lock=obj(E/(a+'-lock-check.json'));require(lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a+': lock drift')
  require(not obj(E/(a+'-source-check.json'))['errors'],a+': source drift')
  for name,h in r['source_hashes'].items():require(sha(E/a/'sources'/name)==h,a+': source snapshot '+name)
 require(rows[41]['exit_status']!=0 and 'timed out' in (E/'NFM_K041/stdout.log').read_text(),'timeout disposition drift')
 replacement=obj(E/'NFM_TIMEOUT_REPLACEMENT.json');require(not replacement['caps_changed'] and not replacement['unchanged_rerun'],'timeout was rerun unchanged')
 # All original scratch hash-gate inputs resolve to immutable committed blobs
 # or the small captured extra-input table. No historical corpus is duplicated.
 inputs=obj(E/'NFM_COMMITTED_INPUTS.json');extra=obj(E/'NFM_EXTRA_INPUTS.json')
 pins=obj(E/'NFM_NATIVE_SOURCE_IMPORTS.json')['files'];available={r['path']:r['sha256'] for r in inputs['committed']}
 for r in extra:require(hashlib.sha256(r['text'].encode()).hexdigest()==r['sha256'],'extra input drift');available[r['path']]=r['sha256']
 require(available==pins,'uncommitted gate input')
 return dict(status='PASS_AD_CONTROL_WINDOWS_FRAMES',attempts=100,groups=groups,excluded={'NFM_K041':'fixed90s solver timeout; no credit'},unused_copy_controls=['NFM_K039','NFM_K040'],option_fn_credits=[],writable_static_credits=[],contracts=[],newly_closed=[],source_inputs=len(available),control_terms=26,active_outer_cuts=7,terminal_outer_state=7)
if __name__=='__main__':
 x=check();(E/'NFM_NATIVE_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(status=x['status'],groups=len(x['groups']),attempts=x['attempts'])))
