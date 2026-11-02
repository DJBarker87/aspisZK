"""Strict additional gates for the admitted fixed800 contract interface.
The original native_pair gate continues to reject every stub_verified source.
"""
import json,hashlib,re

def run(a,want,v):
 try:
  E=v.E;r=v.read(E/a/'receipt.json');cfg=v.read(E/(a+'.json'));log=(E/a/'stdout.log').read_text()
  assert r['kind']=='kani' and (r['exit_status']==0)==want
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert int(r['swaps'])==0 and int(r['peak_rss_kib'])>0 and float(r['wall_seconds'])>0
  assert ('VERIFICATION:- SUCCESSFUL' if want else 'VERIFICATION:- FAILED') in log
  assert 'timed out' not in log.lower() and 'internal compiler error' not in log.lower()
  if not want:assert 'Failed Checks:' in log
  ad=v.read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
  graph=v.read(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
  lock=v.read(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  features=v.read(E/(a+'-metadata-pin.json'))['features_all_crates'];assert features
  actual=next(p['features'] for p in features if p['name']=='aspis-statement');assert set(cfg['required_statement_features'])<=set(actual)
  assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert not v.read(E/(a+'-source-check.json'))['errors'] and v.read(E/(a+'-rule16-check.json'))['no_writable_static']
  code=''
  for n in ['NEM_native_contracts.patch','NEM_oracle.patch']:
   b=(E/(a+'-'+n)).read_bytes();assert r['source_hashes'][n]==hashlib.sha256(b).hexdigest();code+=b.decode()
  assert not re.search(r'\bstatic\s+mut\b|UnsafeCell|RefCell|Atomic|Option\s*<\s*fn|\bas\s+fn\s*\(',code)
  assert 'fn weak(_s:&PoolV1PairLiveSnapshotV1,out:&mut[u8;800],b:bool)' in code
  assert '#[kani::requires(out.len()==800)]' in code
  assert set(re.findall(r'#\[kani::stub_verified\(([^)]+)\)\]',code))<={'weak'}
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False

def fidelity(q,v):
 try:
  expected={'contract':'NEM_K089','real':'NEM_K090','unimplied':'NEM_K091','inverted':'NEM_K092','frame':'NEM_K093','oracle_contract':'NEM_K094','oracle_inverted':'NEM_K095','caller':'NEM_K096','wrong_window':'NEM_K097','inside_unimplied':'NEM_K098'}
  assert q==expected
  assert all(run(a,k in {'contract','real','oracle_contract','caller'},v) for k,a in q.items())
  def code(a):return (v.E/(a+'-NEM_native_contracts.patch')).read_text()
  def weak(a):return next(l for l in code(a).splitlines() if l.startswith('+fn weak('))
  assert weak(q['real'])==weak(q['unimplied'])==weak(q['contract'])==weak(q['inverted'])==weak(q['frame'])
  assert '#[kani::stub_verified(weak)]' not in code(q['real']) and '#[kani::stub_verified(weak)]' in code(q['unimplied'])
  assertion='assert!(out[799]==old,"unimplied full slice mutation frame")'
  assert assertion in code(q['real']) and assertion in code(q['unimplied'])
  assert '#[kani::modifies(&mut out[1])]' in code(q['frame'])
  assert 'assignable' in (v.E/q['frame']/'stdout.log').read_text()
  assert '#[kani::ensures(|r| !(' in code(q['inverted'])
  assert '#[kani::ensures(|r| true)]' in code(q['oracle_contract'])
  assert '#[kani::ensures(|r| !(true))]' in code(q['oracle_inverted'])
  assert weak(q['caller'])==weak(q['oracle_contract'])
  assert 'let array:&mut[u8;800]=window.try_into().unwrap();assert!(array.as_mut_ptr()==expected' in code(q['caller'])
  assert '&mut out[32..32+800]' in code(q['caller']) and '&mut out[33..33+800]' in code(q['wrong_window'])
  assert 'unimplied caller inside window value' in code(q['inside_unimplied'])
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError,StopIteration):return False
