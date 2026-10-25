#!/usr/bin/env python3
"""Read-only source/receipt checker for raw-store leaves, not whole Claims."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-claims-raw-write-20261025';T=R/'tools/s1-claims-raw-write-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.o','.a','.so','.dylib','.rlib','.rmeta'],rel
b=json.loads((P/'source-binding.json').read_text());freeze=b['freeze'];src=subprocess.check_output(['git','show',freeze+':'+b['source_path']],cwd=R);assert hashlib.sha256(src).hexdigest()==b['source_sha256'];s=src.decode();start=s.index('fn claims(');end=s.index('\n#[inline(never)]',start);body=s[start:end];assert hashlib.sha256(body.encode()).hexdigest()==b['claims_body_sha256'];assert b['frozen_loop'] in body
field=subprocess.check_output(['git','show',freeze+':crates/aspis-core/src/field.rs'],cwd=R);assert hashlib.sha256(field).hexdigest()==b['field_source_sha256']
current=(T/'proofs.rs').read_text();assert 'kani::assume' not in current and '#[kani::stub(' not in current and 'transmute' not in current
assert 'out.cast::<[QM31;29]>().add(p).write(rows[p]);' in current
assert 'let actual=out.cast::<QM31>().add(j).read();let expected=rows[j/29][j%29];' in current
# Native jobs use full source and actual raw alloc/dealloc. Allocation-success
# is an explicit domain (Kani default no-malloc-may-fail), not a failure theorem.
for n in range(1,11):
 d=E/f's1-claims-raw-write-v{n}';i=json.loads((d/'input.json').read_text());j=json.loads((d/'receipt.json').read_text())
 assert j['verification_launched']==(n%2==0)
 assert all(j['source_unchanged'].values()) and all(j['tools_unchanged'].values())
 cmd=j['command'];assert 'uninit-checks' in cmd and '--unwinding-assertions' in cmd and '-j' in cmd and cmd[cmd.index('-j')+1]=='1'
 assert i['environment']['RUSTFLAGS']=='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes'
 assert i['guard']==dict(aggregate_rss_limit_bytes=2*2**30,wall_limit_seconds=180,process_limit=64,one_job=True,local_shared_lock=True)
 for name,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(d/name)==j[key]
 for f in (d/'source').rglob('*'):
  if f.is_file() and f.name!='run.py':assert sha(f)==i['source_files'][str(f.relative_to(d/'source'))]
 assert (d/'source/min/src/probe_claims_raw_write.rs').read_bytes()==(T/'probe.rs').read_bytes()
 for row in i['source_binding']['native_source_files']:
  assert i['source_files'][row['path']]==row['sha256']
  if row['source']=='crates/aspis-core/src/field.rs':assert row['sha256']==b['field_source_sha256']
 if n==2:
  assert j['watchdog_stop']=='aggregate RSS watchdog' and j['exit_status']!=0
  continue
 assert j['watchdog_stop'] is None and j['swaps']==0
 assert j['exit_status']==(1 if n==6 else 0)
 if n in [4,8,10]:
  log=(d/'stdout.log').read_text();checks={4:109,8:114,10:142}[n]
  assert f'0 of {checks} failed' in log and '2 of 2 cover properties satisfied' in log and 'VERIFICATION:- SUCCESSFUL' in log
 if n==6:
  log=(d/'stdout.log').read_text();assert 'Reading from an uninitialized pointer' in log and 'VERIFICATION:- FAILED' in log
# The generic byte-coverage model is explicitly not native heap correspondence.
d=E/'s1-claims-raw-write-ranges-v3';j=json.loads((d/'receipt.json').read_text());q=B/'lean-candidates/s126-caller-boundary-20261021/S1ClaimsRawWriteRangesV1.lean'
assert j['exit_status']==0 and j['swaps']==0 and j['source_sha256']==sha(q)==sha(d/'source.lean')
assert len(j['print_axioms'])==7 and all('sorryAx' not in a for a in j['print_axioms'])
for a in j['print_axioms']:
 if 'depends on axioms:' in a:assert set(re.search(r'\[(.*)\]',a)[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'(?m)^\s*(axiom|set_option (maxHeartbeats|maxRecDepth))\b|\b(sorry|native_decide|bv_decide)\b',q.read_text())
print(f'PASS {len(m["files"])} source/evidence pins: native raw-row and original raw-loop initialization leaves + byte-range/coverage model. Original Box/decoder/allocator/SDK/release composition and S1/S6 remain OPEN.')
