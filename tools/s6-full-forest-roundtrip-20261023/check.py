#!/usr/bin/env python3
"""Audit source-only native packets without repeating verification."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s6-full-forest-native'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rev='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
for folder,status in [('semantic-projection',0),('excluded-header-timeout',1)]:
 O=E/folder;manifest=load(O/'manifest.json');rec=load(O/'attempt/receipt.json')
 assert manifest['exit_status']==rec['exit_status']==status
 assert rec['swaps']==0 and rec['limits']['memory.swap.max']=='0'
 assert rec['limits']['memory.max']=='8589934592'
 for f,h in manifest['files'].items():assert sha(O/f)==h,(folder,f)
 assert all(load(O/'attempt/all-local-after.json')['unchanged'].values())
 assert all(load(O/'attempt/dependency-postcheck.json')['unchanged'].values())
 inp=load(O/'attempt/input.json');assert sha(O/'runner.py')==inp['runner_sha256']
 assert '-C opt-level=3' in inp['env']['RUSTFLAGS'] and '-Z mir-opt-level=0' in inp['env']['RUSTFLAGS']
 assert '--solver' in rec['command'] and 'cadical' in rec['command']
 assert '--unwinding-assertions' in rec['command']
 binding=load(O/'input/frozen-statement-binding.json');assert binding['revision']==rev
 for name,h in binding['source_files'].items():
  p=O/'input/frozen-source/crates/aspis-statement'/name
  assert sha(p)==h
  b=subprocess.check_output(['git','-C',str(R),'show',rev+':crates/aspis-statement/'+name]);assert hashlib.sha256(b).hexdigest()==h
 for name,h in binding['external_source_files'].items():assert sha(O/'input/frozen-source'/name)==h
 proof=(O/'input/src/lib.rs').read_text();assert '#[kani::stub' not in proof
 log=(O/'attempt/stdout.log').read_text()
 if status==0:
  assert '0 of 20 failed' in log and '2 of 2 cover properties satisfied' in log
  assert 'core::ptr::eq(public,payment)' in proof and 'core::ptr::eq(&common.lane_transition,transition)' in proof
 else:assert 'CBMC timed out' in log
print(json.dumps(dict(native_semantic_getter_same_complete_fields=True,native_checks=20,covers=2,
 full_codec_roundtrip=False,original_codec_gate_timed_out=True,source_freeze=rev,
 sdk_stage1_binding=False,whole_s1_closed=False,whole_s6_closed=False)))
