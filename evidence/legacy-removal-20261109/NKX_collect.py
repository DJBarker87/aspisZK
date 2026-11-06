"""Check collected native receipts against frozen/final sources and artifact pins."""
from NKX_source import *
import re
validation=json.loads((E/'NKX_SOURCE_VALIDATION.json').read_text())
modes=['baseline','baseline2','tests-deployed','tests-deployed2','tests-default','tests-disabled','tests-all','pool1','pool2','default','devnet']
receipts={};attempts=[]
for mode in modes:
 p=E/('NKX_'+mode)/'receipt.json'
 if not p.exists():continue
 x=json.loads(p.read_text());receipts[mode]=x
 assert x['lock_before']==x['lock_after']==validation['cargo_lock_sha256']
 expected_pool=mode not in ['baseline','baseline2','tests-deployed']
 mismatches=[]
 for path,h in x['source_manifest'].items():
  if mode=='tests-deployed' and path.startswith('programs/aspis-pool/'):
   expected=sha(subprocess.check_output(['git','show','bf38bb69dbe:'+path],cwd=R))
  elif path.startswith('programs/aspis-pool/') and expected_pool:
   expected=validation['source_manifest'].get(path)
  else:expected=sha(frozen(path))
  if h!=expected:mismatches.append(path)
 assert not mismatches,(mode,mismatches)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 if mode not in ['baseline','tests-deployed']:assert x['exit_status']==0,(mode,x['exit_status'])
 attempts.append(dict(attempt=mode,kind='BUILD_TEST_SCOPE',source_revision=x['source_revision'],source_tree_dirty=expected_pool and mode.startswith('tests'),source_manifest_sha256=sha(json.dumps(x['source_manifest'],sort_keys=True).encode()),command=x['target'],exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],limits=x['limits'],cgroup_memory_peak_bytes=x['cgroup_memory_peak_bytes'],lock_before=x['lock_before'],lock_after=x['lock_after'],print_axioms=x['print_axioms'],receipt=str(p.relative_to(E))))
# Reservations are evidence, not build scopes. Preserve admission failures too.
for p in sorted((E/'NKX_admission').glob('*.json')) if (E/'NKX_admission').exists() else []:
 x=json.loads(p.read_text());attempts.append(dict(kind='ADMISSION',receipt=str(p.relative_to(E)),allowed=x.get('allowed'),utc=x.get('utc'),scope_launched=False if not x.get('allowed') else 'see corresponding barrier/receipt',print_axioms='N/A'))
(E/'NKX_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in attempts))
assert len(receipts)<=12
if 'tests-all' in receipts:
 log=(E/'NKX_tests-all/stdout.log').read_text();ran=set(re.findall(r'^test (\S+) \.\.\. ok',log,re.M));x=json.loads((E/'NKX_BYTE_IDENTITY.json').read_text());expected={k.split('/src/',1)[1].replace('.rs::','::') for k in x['tests_after']};assert expected==ran,(expected-ran,ran-expected)
 (E/'NKX_TEST_COVERAGE.json').write_text(json.dumps(dict(status='PASS',static_remaining_tests=len(expected),executed_tests=len(ran),missing=[],unexpected=[],test_names=sorted(ran),pair_forest_integration_tests=sorted(n for n in ran if n.startswith(('pair_forest::','pair_processor::')))),indent=1)+'\n')
if all(k in receipts for k in ['pool1','pool2','default','devnet']):
 def artifact(mode):
  a=receipts[mode]['artifacts'];assert len(a)==1
  return a[0]
 p1=artifact('pool1');p2=artifact('pool2');assert p1['sha256']==p2['sha256'];assert p1['bytes']==p2['bytes']
 pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'}
 for m,h in pins.items():assert artifact(m)['sha256']==h,(m,artifact(m))
 (E/'NKX_ELF.json').write_text(json.dumps(dict(status='PASS',frozen_revision=F,source_revision=receipts['pool1']['source_revision'],pool_sha256=p1['sha256'],pool_bytes=p1['bytes'],pool_reproducible=True,pool_builds={m:dict(artifact=artifact(m),receipt='NKX_'+m+'/receipt.json',exit=receipts[m]['exit_status'],wall_seconds=receipts[m]['wall_seconds'],peak_rss_kib=receipts[m]['peak_rss_kib'],swaps=receipts[m]['swaps']) for m in ['pool1','pool2']},verifiers={m:dict(expected_sha256=h,actual_sha256=artifact(m)['sha256'],identical=True,bytes=artifact(m)['bytes'],receipt='NKX_'+m+'/receipt.json') for m,h in pins.items()},recipe='ELa_build.py native Linux deployed features; private source/target/output; same pinned wrapper/toolchain; CPU affinity 0-3; pool2 removes only own Pool fingerprint/object before codegen',key_policy='Non-key directory placeholders suppress build-sbf key generation; no key files accessed or created.',print_axioms='N/A: engineering only'),indent=1)+'\n')
print('NKX collected receipt gates passed:',len(receipts),'scopes')
