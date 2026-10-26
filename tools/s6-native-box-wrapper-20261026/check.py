#!/usr/bin/env python3
"""Audit all25 native field families; no decoder/SDK/runtime closure claim."""
from pathlib import Path
import base64,hashlib,json,re,subprocess,sys,tomllib
R=Path(__file__).resolve().parents[2];D=Path(__file__).parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
O=E/(sys.argv[1] if len(sys.argv)>1 else 's6-native-box-wrapper-terminal-v1')
sha=lambda b:hashlib.sha256(b).hexdigest();load=lambda p:json.loads(p.read_text())
pins=load(O/'packet-pins.json');assert not pins['binary_files_included']
for name,h in pins['files'].items():
 p=O/name;assert p.suffix in ['.json','.jsonl','.py','.rs','.toml','.lock','.log','.txt']
 assert sha(p.read_bytes())==h,name
for p in D.iterdir():
 if p.is_file() and p.suffix in ['.py','.rs']:assert p.read_bytes()==(O/'tools/current'/p.name).read_bytes(),p.name
subprocess.run([sys.executable,str(D/'generate.py'),'--check'],cwd=R,check=True,stdout=subprocess.DEVNULL)
V=O/'proof-variants/field-cases';binding=load(V/'binding.json');registry=load(V/'registry-pins.json')
assert binding['release_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
assert binding['registry_package_count']==len(registry)==52
assert sum(map(len,binding['proof_only_arbitrary_derives'].values()))==7
attribute=binding['derive_attribute'].encode();assert attribute==b'#[cfg_attr(kani, derive(kani::Arbitrary))]\n'
for path,h in binding['original_source_pins'].items():
 original=subprocess.check_output(['git','show',binding['release_revision']+':'+path],cwd=R)
 assert sha(original)==h
 if path in binding['proof_only_arbitrary_derives']:
  changed=(O/'native-source'/path).read_bytes()
  assert changed.count(attribute)==len(binding['proof_only_arbitrary_derives'][path])
  assert changed.replace(attribute,b'')==original
  assert sha(changed)==binding['files'][path]
 elif path in binding['manifest_changes']:
  patch=binding['manifest_changes'][path]
  assert sha(original)==patch['before_sha256']
  suffix=patch['omitted_suffix'].encode();assert original.endswith(suffix)
  after=original[:-len(suffix)] if suffix else original
  assert sha(after)==patch['after_sha256']==binding['files'][path]
 else:assert binding['files'][path]==h
frozen=tomllib.loads(subprocess.check_output(['git','show',binding['release_revision']+':Cargo.lock'],cwd=R,text=True))
checksums={(p['name']+'-'+p['version']):p.get('checksum') for p in frozen['package']}
assert all(meta['checksum']==checksums[pkg] for pkg,meta in registry.items())
assert registry['solana-program-error-2.2.2']['checksum']=='9ee2e0217d642e2ea4bee237f37bd61bb02aec60da3647c48ff88f6556ade775'
assert sha((V/'sdk-reexport.rs').read_bytes())==binding['sdk_reexport_sha256']
assert b'solana_program_error::ProgramError,' in (V/'sdk-reexport.rs').read_bytes()
proof=(V/'harness/src/lib.rs').read_text();assert proof==(D/'proofs.rs').read_text()
# Preserve the entire actual wrapper signature/body, with the SAME SDK type.
def function(s,name):
 starts=list(re.finditer(r'\bfn '+re.escape(name)+r'\(',s));assert len(starts)==1
 a=starts[0].start();i=s.index('{',a);j=i+1;depth=1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a:j]
actual=subprocess.check_output(['git','show',binding['release_revision']+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],cwd=R,text=True)
assert function(actual,'decode_public_statement_box')==function(proof,'decode_public_statement_box')
assert 'kani::assume' not in proof and 'transmute' not in proof
assert proof.count('#[kani::stub(')==27
assert all('decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return' in line for line in proof.splitlines() if '#[kani::stub(' in line)
assert 'CALLS==1' in proof and 'SEEN==bytes.as_ptr()' in proof and 'LENGTH==bytes.len()' in proof
assert 'ProgramError::InvalidAccountData' in proof and 'drop(after)' in proof
assert 'core::ptr::eq(p,public)' in proof and 'core::ptr::eq(lane,&common.lane_transition)' in proof
assert 'let answer=if kani::any::<bool>() {Ok(arbitrary_statement())} else {Err(kani::any::<FormatError>())}' in proof
for i in range(25):
 assert function(proof,'native_boxed_decoder_family_'+str(i)).endswith('{run(false,'+str(i)+');}')
# Input construction retains independent bytes, no finite content fixture.
assert function(proof,'byte32').count('kani::any::<u8>()')==32
assert function(proof,'byte24').count('kani::any::<u8>()')==24
factory=function(proof,'bytes1880');assert factory.count('byte32()')==58 and factory.count('byte24()')==1
for i in range(58):assert 'bytes['+str(32*i)+'..'+str(32*(i+1))+'].copy_from_slice(&byte32());' in factory
assert 'bytes[1856..1880].copy_from_slice(&byte24());' in factory
accepted=[];total_assertions=0;max_rss=0;max_wall=0;times=0;headers=[]
for i in range(25):
 version='v7' if i<14 else 'v9';case='family'+str(i);A=O/version/case
 plan=load(O/version/'plan.json')
 assert plan['files']['harness/src/lib.rs']==sha(proof.encode())
 assert plan['files']['binding.json']==sha((V/'binding.json').read_bytes())
 for phase in ['compile','verify']:
  receipt=load(A/(phase+'-receipt.json'));inp=load(A/(phase+'-input.json'))
  assert receipt['exit_status']==0 and receipt['source_unchanged'] and receipt['imports_unchanged'] and receipt['tools_unchanged'] and receipt['swaps']==0
  assert inp['source_pins']==plan['files'] and inp['tool_pins'] and inp['import_pins']
  assert inp['environment']['CARGO_BUILD_JOBS']=='1'
  assert '-C opt-level=3' in inp['environment']['RUSTFLAGS'] and '-C overflow-checks=yes' in inp['environment']['RUSTFLAGS']
  assert receipt['command']==inp['command'] and '--harness-timeout' in receipt['command']
  assert 'proofs::native_boxed_decoder_family_'+str(i) in receipt['command']
  assert not any(flag in receipt['command'] for flag in ['--no-memory-safety-checks','--no-unwinding-assertions'])
  for pkg,meta in inp['import_pins'].items():
   assert meta['checksum']==registry[pkg]['checksum'] and meta['files']==registry[pkg]['files']
  assert set(inp['import_pins'])==set(registry)
  cg=receipt['cgroup'];assert cg['memory.max']==str(2*2**30) and cg['memory.high']==str(1792*2**20) and cg['memory.swap.max']=='0'
  events=dict(line.split() for line in cg['memory.events'].splitlines());assert events['oom']=='0' and events['oom_kill']=='0'
  admission=load(A/(phase+'-admission.json'));assert admission['admitted'] and admission['own_scope_included']
  if phase=='verify':
   max_rss=max(max_rss,receipt['peak_rss_kib']);max_wall=max(max_wall,receipt['wall_seconds']);times+=receipt['wall_seconds']
  headers.append((inp['source_pins'],inp['tool_pins'],inp['import_pins']))
 output=(A/'verify-stdout.log').read_text()
 assert 'VERIFICATION:- SUCCESSFUL' in output and '** 3 of 3 cover properties satisfied' in output
 count=re.search(r'\*\* 0 of (\d+) failed',output);assert count
 total_assertions+=int(count[1]);accepted.append(i)
 assert load(A/'terminal.json')['exit_status']==0
 # The launched wrapper is separately pinned, rather than confusing it with
 # the unused runner file retained in the build-input snapshot.
 assert load(A/'launch.json')['runner_sha256']==sha((O/version/'nuc.py').read_bytes())
assert all(h==headers[0] for h in headers)
assert accepted==list(range(25))
# Failed preflights and whole-target attempts stay visibly excluded.
for version in ['v2','v7','v8']:
 case='positive' if version=='v2' else 'family14'
 assert not load(O/version/case/'admission-before-scope.json')['admitted']
 assert not (O/version/case/'compile-receipt.json').exists()
for version in ['v4','v5']:
 r=load(O/version/'positive/verify-receipt.json');assert r['exit_status']==124 and r['swaps']==0
 assert 'Checking harness proofs::native_boxed_decoder_projection' not in (O/version/'positive/verify-stdout.log').read_text()
r=load(O/'v6/positive/verify-receipt.json');assert r['exit_status']!=0 and r['swaps']==0
assert 'CBMC timed out' in (O/'v6/positive/verify-stdout.log').read_text()
assert not load(O/'v5/resource-review.json')['changed']
for version in ['v5','v6','v7']:
 update=load(O/version/'source-update.json');r=load(O/version/'source-update-receipt.json')
 assert r['exit_status']==0 and r['before_pins_verified'] and r['after_pins_verified'] and not r['native_crates_changed'] and r['build_cache_preserved']
 assert set(update['changes'])=={'binding.json','harness/src/lib.rs'}
 for path,encoded in update['changes'].items():assert sha(base64.b64decode(encoded))==update['after'][path]
# Negative control is a distinct native aarch64/darwin diagnostic. It does
# not fill any missing Linux positive family or establish cross-target replay.
N=O/'local/s6-native-box-wrapper-negative-local-v1';n=load(N/'receipt.json');ni=load(N/'input.json')
assert n['exit_status']==1 and n['swaps']==0 and n['watchdog_stop'] is None
assert n['source_unchanged'] and n['imports_unchanged'] and n['tools_unchanged'] and n['verification_launched']
assert ni['source_pins']['harness/src/lib.rs']==sha(proof.encode())
assert ni['guard']['aggregate_rss_max_bytes']==4*2**30
output=(N/'stdout.log').read_text();assert '** 1 of 769 failed' in output and '** 3 of 3 cover properties satisfied' in output
assert 'Failed Checks: assertion failed: observe(&before,family,i,j)==observe(&after,family,i,j)' in output
assert 'CBMC timed out' not in output
print(json.dumps({'status':'PASS','linux_field_families':accepted,'transfer_scalar_coordinates':608,'withdrawal_scalar_coordinates':633,'total_assertions':total_assertions,'max_verify_rss_kib':max_rss,'max_verify_wall_seconds':max_wall,'sum_verify_wall_seconds':times,'negative_control':'intended scalar assertion fails; distinct aarch64/darwin target','native_decoder_cut_retained':True,'default_malloc_success_no_uninit_check_model':True,'whole_s6_closed':False,'enclosing_source_caller_premises_removed':0}))
