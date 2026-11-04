"""No composed credit. Audit only terminal native packets and exclusions."""
from NET_window_certificates import *
import NET_geometry_source as source
import NET_geometry_window_source as window

def audit():
 failed=[]
 for a in ['NET_K089','NET_K090','NET_K091']:
  r=obj(E/a/'receipt.json');log=(E/a/'stdout.log').read_text()
  assert 'timed out' in log.lower() and r['exit_status']!=0
  assert r['limits']==CAPS and int(r['swaps'])==0
  assert obj(E/(a+'-lock-check.json'))['unchanged']
  failed.append(dict(attempt=a,disposition='EXCLUDED_TIMEOUT; no pass, no unchanged rerun',wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib']))
 accepted=[]
 for i,want in [(92,0),(93,1),(94,0),(95,1),(96,0),(97,1),(98,1),(99,0),(100,1)]:
  a=f'NET_K{i:03}';p=E/a/'receipt.json'
  assert p.exists(),a
  r=check(a,want);d=inputs(a)
  assert d['NET_src/crates/aspis-r1-cost-probe/src/verifier/NET_geometry.rs']==(E/'NET_geometry.rs.txt').read_text()
  assert r['source_hashes']==obj(E/'NET_K092/receipt.json')['source_hashes']
  assert obj(E/(a+'-graph-check.json'))['resolved_features_all_crates']==obj(E/'NET_K092-graph-check.json')['resolved_features_all_crates']
  env=dict(r['env']);env['RUSTFLAGS']=re.sub(r' --cfg NET_(one_push|bad_reply|bad_argument)','',env['RUSTFLAGS'])
  base=dict(obj(E/'NET_K096/receipt.json')['env']);assert env==base
  accepted.append(dict(attempt=a,exit_status=r['exit_status'],target=r['target'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib']))
 return dict(status='PARTIAL_ONLY; no new composed row or incoming edge',excluded=failed,accepted=accepted,source=window.check_window(),inverse_native_child='OPEN',reserve_native='OPEN after isolated K091 timeout',scope='Current TX1/TX2 one-push windows and a single reverse-cell log; whole geometry remains OPEN')
if __name__=='__main__':
 d=audit();(E/'NET_PARTIAL_GEOMETRY.json').write_text(json.dumps(d,indent=1)+'\n');print(json.dumps(d))
