#!/usr/bin/env python3
"""Read/hash-only native evidence verification. Never runs Rust or Lean."""
from pathlib import Path,PurePosixPath
import hashlib,io,json,re,subprocess,tarfile
here=Path(__file__).resolve().parent;root=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
def unpack(raw):
 with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as t:
  members=t.getmembers();assert len({x.name for x in members})==len(members)
  for x in members:assert x.isfile() and not PurePosixPath(x.name).is_absolute() and '..' not in PurePosixPath(x.name).parts
  return {x.name:t.extractfile(x).read() for x in members}
m=json.loads((here/'manifest.json').read_text());raw=(here/m['archive']).read_bytes();assert sha(raw)==m['archive_sha256'] and len(raw)==m['archive_bytes']
d=unpack(raw);assert len(d)==m['entries'];j=lambda n:json.loads(d[n])
pins=dict(x.split('  ',1)[::-1] for x in d['SHA256SUMS'].decode().splitlines());assert set(pins)==set(d)-{'SHA256SUMS'}
for n,h in pins.items():assert sha(d[n])==h,n
assert d['pack.py']==(here/'pack.py').read_bytes()
snapshots={};manifests={}
for side in ['after','before','combined','combined-fixed']:
 p=j(side+'-manifest.json');manifests[side]=p;assert sha(d[side+'.tar.gz'])==p['archive_sha256']
 files=unpack(d[side+'.tar.gz']);snapshots[side]=files;assert set(files)==set(p['files'])
 for n,b in files.items():
  assert sha(b)==p['files'][n]
  original=subprocess.check_output(['git','-C',str(root),'show',p['source_revision']+':'+n])
  if n in p.get('instrumentation_changes',{}):
   a=p['instrumentation_changes'][n];assert sha(original)==a['original_sha256'] and sha(b)==a['instrumented_sha256']
   candidate=snapshots['after'][n];assert sha(candidate)==a['candidate_source_sha256']
   s=candidate.decode();start=s.index('#[derive(Clone, Copy)]\nstruct CountedDigest;');end=s.index('static PHASE:',start)
   assert b==(s[:start]+s[end:]).replace(', CountedDigest, None',', counted_hash, None').encode()
  else:assert b==original,(side,n)
# Current production files retain the tested combined source; docs may advance.
for n,b in snapshots['combined-fixed'].items():assert (root/n).read_bytes()==b,n
changed=[n for n,b in snapshots['combined'].items() if b!=snapshots['combined-fixed'][n]]
assert changed==['programs/r1-cost-probe/src/r1_checkpoint_tests.rs']
summary=j('SUMMARY.json');assert summary==m['summary'];assert len(summary['targets'])==11
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
for label,row in summary['targets'].items():
 p='runs/'+label+'/';r=j(p+'receipt.json');side=Path(r['cwd']).name;manifest=manifests[side]
 assert r['exit']==0 and r['limits']==limits and r['swap_current_bytes']==0 and r['process_swaps']==0
 assert r['source_manifest_sha256']==sha(d[side+'-manifest.json']) and r['source_revision']==manifest['source_revision']
 assert r['stdout_sha256']==sha(d[p+'stdout.log']) and r['stderr_sha256']==sha(d[p+'stderr.log'])
 assert r['runner_sha256']==sha(d[p+'run-native.py'])
 for k in ['source_revision','exit','wall_seconds','peak_rss_kib','cgroup_peak_bytes','swap_current_bytes','process_swaps','artifacts']:assert row[k]==r[k]
 for dep,pin in r['dep_info'].items():assert sha(d[p+'dep-info/'+Path(dep).name])==pin['sha256']
 audit=j(p+'resolved-dep-info-audit.json');assert set(audit)==set(r['dep_info'])
 for dep,entry in audit.items():
  for x in entry['resolved_and_rehashed']:
   if 'source' in x:assert sha(snapshots[side][x['source']])==x['sha256']
   else:
    assert sha(d[x['retained_path']])==x['sha256'] and len(d[x['retained_path']])==x['bytes']
    assert all(q['files'][x['generator_source']]==x['generator_sha256'] for q in manifests.values())
 # Preserve each actual binary and compiler command pin; blobs remain on host.
 if label!='examples-typecheck':assert r['artifacts']
 if 'expected_tests' in r and not r.get('validation_failure'):assert r['passed_test_counts']==[r['expected_tests']] and r['expected_tests']>0
 if r.get('validation_failure'):assert label=='checkpoint-counts-run' and r['passed_test_counts']==[23] and r['expected_tests']==27
 stdout=d[p+'stdout.log'].decode()
 if label.startswith('schedule-'):assert 'test concrete_sha256_constructor_rows_reseed_queries_and_rho_keep_exact_calls ... ok' in stdout
 if label.startswith('readonly-'):
  for name in ['accepts_equal_owner_values','rejects_executable','rejects_signer','rejects_writable','rejects_wrong_owner']:assert 'readonly_metadata_'+name+' ... ok' in stdout
c=j('checkpoint-test-count-correction.json');source=snapshots['combined-fixed']['programs/r1-cost-probe/src/r1_checkpoint_tests.rs']
assert sha(source)==c['source_sha256'];expected=re.findall(r'#\[test\]\s*fn\s+(\w+)',source.decode())
actual=re.findall(r'test r1_pool_adapter::checkpoint_tests::(\w+) \.\.\. ok',d['runs/checkpoint-counts-run/stdout.log'].decode())
assert len(expected)==23 and set(expected)==set(actual)==set(c['expected_from_source'])==set(c['passed_names'])
assert 'measured_core_call_counts_include_zero_progress_checkpoint' in actual
assert c['observed_wrapper_exit_status']==105 and c['cargo_child_exit_status']==0 and c['rerun_performed'] is False
assert c['receipt_sha256']==sha(d['runs/checkpoint-counts-run/receipt.json'])
for label in summary['failed_receipts_retained']:assert 'runs/'+label+'/receipt.json' in d
assert j('runs/checkpoint-counts-fixed/receipt.json')['exit']==0 and 'test result: ok. 0 passed;' in d['runs/checkpoint-counts-fixed/stdout.log'].decode()
a=j('before-ordered-counter.json');b=j('after-ordered-counter.json')
assert a['ordered_digest_calls']==b['ordered_digest_calls'] and len(a['ordered_digest_calls'])==583 and a['acceptance']==b['acceptance']
def counts(x):
 c=dict(x['hash_input_counts']);c['repeated_exact_inputs']=sorted(c['repeated_exact_inputs'],key=lambda v:v['input_hex']);return c
assert counts(a)==counts(b) and a['hash_input_counts']['tx1_raw_calls']==349 and a['hash_input_counts']['tx2_raw_calls']==234
reuse=j('codec-baseline/reuse.json');old=root/'docs/research/100bit-spend-path-20261013/evidence/terminal-validator-extraction-20261016/evidence.tar.gz'
assert sha(old.read_bytes())==reuse['archive_sha256']
with tarfile.open(old) as t:
 for n,h in reuse['retained_files'].items():assert sha(d['codec-baseline/'+n])==h and d['codec-baseline/'+n]==t.extractfile(n).read()
trace=d['runs/codec1233/stdout.log'];assert trace==d['codec-baseline/helper/runs/trace-a/stdout.log']
assert sha(trace)=='3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321' and trace.splitlines()[-1]==b'complete 1233'
print('PASS',len(d),'members; 4 Git-pinned snapshots; 11 native gates; 23 named checkpoint tests; 1233-case byte equality; 583 ordered digest calls/checkpoint identical; CU OPEN')
