"""Validate support receipts only. Never infer a composed row from windows."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
PATCH='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def need(v,m):
 if not v:raise ValueError(m)
def check():
 need(sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')==PATCH,'wrong copy patch')
 attempts=[json.loads(l) for l in (E/'NFP_ATTEMPTS.jsonl').read_text().splitlines()]
 ks=[r for r in attempts if r['kind']=='kani'];need(len(ks)==76,'native budget drift')
 positives={3,5,7,9,12,14,16,18,20,22,25,27,29,30,32,34,36,38,41,43,45,46,48,49,51,52,54,56,58,60,62,64,66,68,70,72,74,75}
 excluded={1,2,11,24,59};validated=[]
 for n in range(1,77):
  a=f'NFP_K{n:03}';r=obj(E/a/'receipt.json');need(r['kind']=='kani' and r['attempt']==a,'wrong receipt')
  admission=obj(E/(a+'-admission.json'));need(admission['exit']==0 and admission['reservation']['allowed'] is True,'scope not admitted')
  need(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'cap drift')
  need(r['swaps']=='0' and int(r['peak_rss_kib'])<8*1024**2,'resource violation')
  if n in excluded:continue
  need(r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3','native environment drift')
  need('--locked' not in r['native_command'] and '--features' in r['native_command'],'Kani command parity')
  need(r['source_hashes']['NFP_KMX.patch']==PATCH,'unpaired patch')
  g=obj(E/(a+'-graph-check.json'));l=obj(E/(a+'-lock-check.json'))
  need(g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors'],'graph drift')
  need(l['unchanged'] and l['before']==l['after']==g['lock_sha256'],'post lock drift')
  need(not obj(E/(a+'-source-check.json'))['errors'],'frozen source change')
  need(not obj(E/(a+'-rule16-check.json'))['static_declarations'],'static state')
  f=obj(E/(a+'-fission-check.json'));need(f['erasure_exact'],'original caller erasure')
  log=(E/a/'stdout.log').read_text();expected=0 if n in positives else 1
  need(r['exit_status']==expected,'unexpected verdict')
  need(('VERIFICATION:- SUCCESSFUL' in log if not expected else 'VERIFICATION:- FAILED' in log),'missing actual verdict')
  need('VERIFICATION:- UNKNOWN' not in log and 'timed out' not in log.lower(),'timeout admitted')
  validated.append(dict(attempt=a,module=r['module'],exit_status=r['exit_status'],receipt_sha256=sha(E/a/'receipt.json'),graph_sha256=g['graph_sha256'],compiled_native_sha256=f.get('compiled_native_source_sha256'),source_hashes={k:v for k,v in r['source_hashes'].items() if k.endswith('.rs.txt')},wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
 by={r['attempt']:r for r in validated};pairs=obj(E/'NFP_RENAME_PAIRS.json')['families']
 for p in pairs:
  ids=[p[k].split()[0] for k in ['positive','renamed','control','copy_control']]
  rows=[by[i] for i in ids];need([r['exit_status'] for r in rows]==[0,0,1,1],'rename/control verdict')
  need(all(r['source_hashes']==rows[0]['source_hashes'] for r in rows),'family payload changed')
  need(all(r['graph_sha256']==rows[0]['graph_sha256'] for r in rows),'family dependency graph changed')
 return dict(status='PASS_LOCAL_SUPPORT_ONLY',attempts=76,validated=len(validated),positives=len(positives),failing_controls=len(validated)-len(positives),excluded=[f'NFP_K{n:03}' for n in sorted(excluded)],rename_families=len(pairs),exact_KMX_patch_sha256=PATCH,field_multiplication_proved_in_Kani=False,query_rows_closed=0,receipts=validated)
if __name__=='__main__':
 r=check();(E/'NFP_NATIVE_VALIDATION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='receipts'}))
