"""Strict local-record native pair checks shared by new additive packets."""
import json,copy,hashlib
from pathlib import Path
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
CAPS=dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
def check(E,pos,neg,cfg,assertion='assert_failed_inner'):
 ds=[obj(E/a/'receipt.json') for a in [pos,neg]]
 assert [d['exit_status'] for d in ds]==[0,1],(pos,neg,'verdict')
 assert ds[0]['source_hashes']==ds[1]['source_hashes'] and ds[0]['native_command']==ds[1]['native_command'],'pair source/command'
 env=copy.deepcopy(ds[0]['env']);env['RUSTFLAGS']+=' --cfg '+cfg;assert env==ds[1]['env'],'pair environment'
 for a,d in zip([pos,neg],ds):
  assert d['kind']=='kani' and d['limits']==CAPS and d['swaps']=='0'
  assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert d['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  for n,h in d['source_hashes'].items():assert sha(E/a/'sources'/n)==h,(a,n)
  assert obj(E/(a+'-graph-check.json'))['graph_matches_frozen']
  lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert obj(E/(a+'-frozen-source-check.json'))['passed']
  assert obj(E/(a+'-rule16-check.json'))['static_declarations']==[]
  assert obj(E/(a+'-tool-check.json'))['version']=='cargo-kani 0.67.0'
  assert all(k in d and d[k] is not None for k in ['source_revision','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes'])
  log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if a==pos else 'VERIFICATION:- FAILED') in log
  assert 'timed out' not in log and 'compilation failed' not in log
  if a==neg:assert '** 1 of ' in log and assertion in log,'control did not fail intended assertion'
 assert obj(E/(pos+'-tool-check.json'))['binaries']==obj(E/(neg+'-tool-check.json'))['binaries'],'pair compiler/backend drift'
 return dict(positive=pos,negative=neg,status='PASS',frozen_graph=True,lock_unchanged=True,rule16=True)
