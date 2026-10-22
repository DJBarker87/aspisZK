#!/usr/bin/env python3
"""Audit selected SDK cuts and snapshot equivalence; not whole S2 closure."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile,tomllib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/sdk-parent-cuts';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={}
def checked(tag,folder,expected_covers=None):
 source=E/'sources'/folder/'src/lib.rs';cut=json.loads((source.parents[1]/'source-cut.json').read_text())
 assert cut['source_sha256']==sha(source)
 inp=json.loads((E/(tag+'-input.json')).read_text());assert inp['source_sha256']==sha(source)
 assert '-C opt-level=3' in inp['env']['RUSTFLAGS'] and 'overflow-checks=yes' in inp['env']['RUSTFLAGS']
 assert inp['env']['CARGO_BUILD_JOBS']=='1' and inp['tool_pins']
 receipt=E/'receipts'/tag/'receipt.json';r=json.loads(receipt.read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert r['limits']['memory.max']=='8589934592' and '--unwinding-assertions' in r['command']
 log=(receipt.parent/'stdout.log').read_text();counts=re.search(r'0 of (\d+) failed',log);assert counts
 covers=re.search(r'(\d+) of (\d+) cover properties satisfied',log);assert covers
 assert (tuple(map(int,covers.groups()))==expected_covers if expected_covers is not None else covers[1]==covers[2])
 packages={p['name']:p for p in tomllib.loads((source.parents[1]/'Cargo.lock').read_text())['package']}
 for p,v in [('solana-program','2.3.0'),('solana-account-info','2.3.0'),('solana-program-error','2.2.2')]:assert packages[p]['version']==v and packages[p]['checksum']
 accepted[tag]=dict(source_sha256=sha(source),receipt_sha256=sha(receipt),assertions=int(counts[1]),covers=int(covers[1]),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=0)
 return source,cut,receipt
for mode in ['shared','exclusive','length','chain']:
 source,cut,_=checked('sdk-heap-'+mode+'-join-v2','sdk-heap-'+mode+'-v2')
 assert cut['max_buffer_bytes']==10485760
 text=source.read_text();assert 'initial_lamport_counts:[isize;3]=kani::any()' in text
 assert 'data_slots:[usize;3]=kani::any()' in text and 'lamport_slots:[usize;3]=kani::any()' in text
 if mode=='chain':assert 'actual_trace[i][row],expected_trace[i][row]' in text and 'lifecycle cut' in cut['domain']
 with tempfile.TemporaryDirectory() as d:
  subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-heap-join.py'),d,mode,'10485760'],check=True)
  assert (Path(d)/'src/lib.rs').read_bytes()==source.read_bytes()
for mode in ['shared','exclusive']:
 source,cut,receipt=checked('sdk-'+mode+'-write-frame-v3','sdk-'+mode+'-write-frame-v3')
 assert cut['all_lamport_counters'] and cut['max_buffer_bytes']==10485760
 text=source.read_text();assert '#[kani::modifies(counter.cast::<isize>())]' in text and '#[kani::proof_for_contract('+mode+'_roundtrip)]' in text
 audit=json.loads((E/'receipts'/('sdk-'+mode+'-write-properties-v3')/'property-audit.json').read_text())
 pins=json.loads((E/('sdk-'+mode+'-properties-v3-input.json')).read_text())
 assert pins['checked_source_sha256']==audit['source_sha256']==sha(source)
 assert pins['checked_receipt_sha256']==sha(receipt) and pins['program_sha256']==audit['checked_program_sha256']
 assert any(p['class']=='assigns' and 'AccountInfo' in p['name'] for p in audit['contract_properties'])
 assert any(p['class']=='assertion' and 'old(' in p['description'] for p in audit['contract_properties'])
 with tempfile.TemporaryDirectory() as d:
  subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-shared-write-frame.py'),d,mode,'all-rc-counts','10485760','all-lamport-counters'],check=True)
  assert (Path(d)/'src/lib.rs').read_bytes()==source.read_bytes()
source,cut,_=checked('sdk-metadata-prefix-join-v2','sdk-metadata-prefix-v2')
assert cut['protocol_freeze']=='b2727acd3abf79315d18b754a260f58f4b1c6326' and cut['max_buffer_bytes']==10485760
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-metadata-prefix.py'),d],check=True)
 assert (Path(d)/'src/lib.rs').read_bytes()==source.read_bytes()
 assert json.loads((Path(d)/'source-cut.json').read_text())==cut
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/make-sdk-metadata-parent.py'),d],check=True)
 assert (Path(d)/'S2SdkMetadataParentV1.lean').read_bytes()==(S/'S2SdkMetadataParentV1.lean').read_bytes()
prefixTag='sdk-prefix-context-check-v3'
prefixSource=E/'sources/sdk-prefix-context-v3/src/lib.rs'
cut=json.loads((prefixSource.parents[1]/'source-cut.json').read_text())
codegen=json.loads((E/'sdk-prefix-context-codegen-v3-input.json').read_text())
assert codegen['source_sha256']==cut['source_sha256']==sha(prefixSource)
assert codegen['env']['RUSTFLAGS'].startswith('-C opt-level=3 ')
rawReceipt=E/'receipts'/prefixTag/'receipt.json';raw=json.loads(rawReceipt.read_text())
assert raw['exit_status']==10 and raw['swaps']==0 and raw['limits']['memory.swap.max']=='0'
properties=json.loads((E/'diagnostics'/prefixTag/'properties-without-traces.json').read_text())
assert properties and all(p['status']=='SUCCESS' for p in properties if p['sourceLocation'].get('propertyClass')!='cover')
covers=[p for p in properties if p['sourceLocation'].get('propertyClass')=='cover']
assert len(covers)==1 and covers[0]['status']=='FAILURE' # raw CBMC counterexample witnesses reachability
inp=json.loads((E/(prefixTag+'-input.json')).read_text())
normal=E/'receipts/sdk-private-stub-semantic-preflight-v4/stdout.log'
assert inp['normal_pipeline_receipt_sha256']==sha(normal)
assert inp['pretty_name'].find('any')>=0 and len(inp['input_goto_sha256'])==64
assert inp['timeout_seconds']==180 and inp['tool_pins']
assert '--unwinding-assertions' in inp['commands'][-1]
assert not any(c in inp['commands'][-1] for c in ['--no-bounds-check','--no-pointer-check','--no-unwinding-assertions'])
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-paired-context.py'),d,'prefix'],check=True)
 assert (Path(d)/'src/lib.rs').read_bytes()==prefixSource.read_bytes()
 assert json.loads((Path(d)/'source-cut.json').read_text())==cut
accepted[prefixTag]=dict(source_sha256=sha(prefixSource),receipt_sha256=sha(rawReceipt),raw_exit_status=10,noncover_successes=len(properties)-len(covers),reachable_covers=1,wall_seconds=raw['wall_seconds'],peak_rss_kib=raw['peak_rss_kib'],swaps=0,qualification='Native frozen stage1 decoder-entry cut, with actual decoder length rejection; native std-any overapproximation remains explicit. Cover counterexample is expected; every non-cover property must be SUCCESS. Not post-decoder/full-stage correspondence.')
callTag='sdk-call-prefix-check-v1'
callSource=E/'sources/sdk-call-context-v1/src/lib.rs'
cut=json.loads((callSource.parents[1]/'source-cut.json').read_text())
codegen=json.loads((E/'sdk-call-prefix-codegen-v1-input.json').read_text())
assert codegen['source_sha256']==cut['source_sha256']==sha(callSource)
assert codegen['env']['RUSTFLAGS'].startswith('-C opt-level=3 ')
rp=E/'receipts'/callTag/'receipt.json';r=json.loads(rp.read_text())
assert r['exit_status']==10 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
properties=json.loads((E/'diagnostics'/callTag/'properties-without-traces.json').read_text())
noncover=[p for p in properties if p['sourceLocation'].get('propertyClass')!='cover']
covers=[p for p in properties if p['sourceLocation'].get('propertyClass')=='cover']
assert noncover and all(p['status']=='SUCCESS' for p in noncover)
assert len(covers)==2 and all(p['status']=='FAILURE' for p in covers)
assert any('successful verifier reply never calls error mapper' in p['description'] for p in noncover)
for text in ['observer.is_none()','proof.as_ptr()','PUBLIC_PARTS[phase][0]','PUBLIC_PARTS[phase][1]','BOX_PTRS[phase]','CANDIDATE_PTRS[phase]']:
 assert any(text in p['description'] for p in noncover),text
inp=json.loads((E/(callTag+'-input.json')).read_text())
assert '--unwinding-assertions' in inp['commands'][-1] and inp['normal_pipeline_receipt_sha256']==sha(normal)
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-paired-context.py'),d,'call','fields','unreachable-error'],check=True)
 assert (Path(d)/'src/lib.rs').read_bytes()==callSource.read_bytes()
 assert json.loads((Path(d)/'source-cut.json').read_text())==cut
 assert (Path(d)/'statement-fields.json').read_bytes()==(callSource.parents[1]/'statement-fields.json').read_bytes()
accepted[callTag]=dict(source_sha256=sha(callSource),receipt_sha256=sha(rp),raw_exit_status=10,noncover_successes=len(noncover),reachable_covers=2,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=0,qualification='Full native SDK tx1-entry prefix. Actual typed object/public/proof/k/None arguments checked; all statement value fields quantified. Reply fixed to Ok(empty Vec), causing following size guard to reject; actual child interpretation/prefix transport and post-child writeback remain explicit. Error mapper reachability assertion is proved, not assumed.')
normalizationTag='sdk-call-prefix-check-v3'
normalizationSource=E/'sources/sdk-call-context-v2/src/lib.rs'
normalizationCut=json.loads((normalizationSource.parents[1]/'source-cut.json').read_text())
normalizationCodegen=json.loads((E/'sdk-call-prefix-codegen-v3-input.json').read_text())
assert normalizationCodegen['source_sha256']==normalizationCut['source_sha256']==sha(normalizationSource)
normalizationReceipt=E/'receipts'/normalizationTag/'receipt.json';nr=json.loads(normalizationReceipt.read_text())
assert nr['exit_status']==10 and nr['swaps']==0 and nr['limits']['memory.swap.max']=='0'
rows=json.loads((E/'diagnostics'/normalizationTag/'properties-without-traces.json').read_text())
noncover=[r for r in rows if r['sourceLocation'].get('propertyClass')!='cover']
covers=[r for r in rows if r['sourceLocation'].get('propertyClass')=='cover']
assert noncover and all(r['status']=='SUCCESS' for r in noncover)
assert len(covers)==2 and all(r['status']=='FAILURE' for r in covers)
assert any('actual tx1-entry derives canonical descriptor slots' in r['description'] for r in noncover)
assert 'let data_slots:[usize;3]=kani::any();' in normalizationSource.read_text()
assert 'ENTRY_SLOTS=data_slots' in normalizationSource.read_text()
ni=json.loads((E/(normalizationTag+'-input.json')).read_text())
assert ni['artifact_selection']['source_sha256']==sha(normalizationSource)
assert ni['artifact_selection']['codegen_input_sha256']==sha(E/'sdk-call-prefix-codegen-v3-input.json')
assert '--unwinding-assertions' in ni['commands'][-1]
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-paired-context.py'),d,'call','fields','unreachable-error','unused','entry-slots'],check=True)
 assert (Path(d)/'src/lib.rs').read_bytes()==normalizationSource.read_bytes()
 assert json.loads((Path(d)/'source-cut.json').read_text())==normalizationCut
accepted[normalizationTag]=dict(source_sha256=sha(normalizationSource),receipt_sha256=sha(normalizationReceipt),raw_exit_status=10,noncover_successes=len(noncover),reachable_covers=2,wall_seconds=nr['wall_seconds'],peak_rss_kib=nr['peak_rss_kib'],swaps=0,qualification='Full actual native tx1-entry cut additionally derives the initial descriptor slot map [0,1,2] from all alias-map inputs. Real statement values, SDK fields/counters and pointer/k/None checks retained. Common successful typed child hooks and fixed empty reply still require actual-child/prefix transport. No whole-stage source or ordered oracle join claimed.')

nativeTag='sdk-native-context-check-v9'
nativeSource=E/'sources/sdk-native-context-v5/src/lib.rs'
nativeCut=json.loads((nativeSource.parents[1]/'source-cut.json').read_text())
nativeCodegen=json.loads((E/'sdk-native-context-codegen-v5-input.json').read_text())
assert nativeCodegen['source_sha256']==nativeCut['source_sha256']==sha(nativeSource)
nativeReceipt=E/'receipts'/nativeTag/'receipt.json';nr=json.loads(nativeReceipt.read_text())
assert nr['exit_status']==10 and nr['swaps']==0 and nr['limits']['memory.swap.max']=='0'
rows=json.loads((E/'diagnostics'/nativeTag/'properties-without-traces.json').read_text())
noncover=[r for r in rows if r['sourceLocation'].get('propertyClass')!='cover']
covers=[r for r in rows if r['sourceLocation'].get('propertyClass')=='cover']
assert noncover and all(r['status']=='SUCCESS' for r in noncover)
assert len(covers)==2 and all(r['status']=='FAILURE' for r in covers)
assert any('actual post-call SDK checkpoint descriptor remains bound to root2' in r['description'] for r in noncover)
assert any('NATIVE_ROOT_PTRS[2].add(observed).read()' in r['description'] for r in noncover)
ni=json.loads((E/(nativeTag+'-input.json')).read_text())
assert ni['artifact_selection']['source_sha256']==sha(nativeSource)
assert ni['artifact_selection']['codegen_input_sha256']==sha(E/'sdk-native-context-codegen-v5-input.json')
assert '--unwinding-assertions' in ni['commands'][-1] and not ni['selected_properties']
assert nativeCut['std_copy_certificate']['leaf_proof']=='sdk-std-copy-frame-join-v1'
assert nativeCut['std_copy_certificate']['bridge_proof']=='sdk-std-copy-bridge-join-v1'
assert 'entry_normalization' in nativeCut and 'constructor_normalization' in nativeCut
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-paired-context.py'),d,'native','fields','unreachable-error','std-copy','normalized-data','canonical-ctor','direct-query'],check=True)
 assert (Path(d)/'src/lib.rs').read_bytes()==nativeSource.read_bytes()
 assert json.loads((Path(d)/'source-cut.json').read_text())==nativeCut
accepted[nativeTag]=dict(source_sha256=sha(nativeSource),receipt_sha256=sha(nativeReceipt),raw_exit_status=10,noncover_successes=len(noncover),reachable_covers=2,wall_seconds=nr['wall_seconds'],peak_rss_kib=nr['peak_rss_kib'],swaps=0,qualification='Full real native SDK stage1 through successful arbitrary1768-byte writeback: actual decoded-object/public/proof/k/None arguments, post-SDK checkpoint descriptor/observed value and all returned counter restorations checked. Input descriptor normalization has its own source-entry certificate. Common successful typed child hooks, actual child/prefix/scan/runtime embedding and full owned/state/log composition remain explicit. This is not an unconditional actual-source or total whole-stage join.')

stepSource,stepCut,stepReceipt=checked('sdk-finish-step-join-v3','sdk-finish-step-v3')
stepText=stepSource.read_text()
assert '#[cfg_attr(kani,kani::modifies(target))]' in stepText
assert 'target:*mut u8' in stepText and 'destination[offset]=source[offset]' in stepText
assert 'target==unsafe{destination.as_mut_ptr().add(offset)}' in stepText
assert 'count/loop' in stepCut['qualification'] and 'not the frozen whole-copy' in stepCut['qualification']
stepAudit=json.loads((E/'receipts/sdk-finish-step-properties-v3/property-audit.json').read_text())
stepPins=json.loads((E/'sdk-finish-step-properties-v3-input.json').read_text())
assert stepAudit['source_sha256']==stepPins['source_sha256']==sha(stepSource)
assert stepAudit['proof_receipt_sha256']==stepPins['proof_receipt_sha256']==sha(stepReceipt)
assert stepAudit['program_sha256']==stepPins['program_sha256']
assert any(p['class']=='assigns' and 'native_copy_step' in p['name'] for p in stepAudit['selected_properties'])
assert any('old(source[offset])' in p['description'] for p in stepAudit['selected_properties'])
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-finish-step.py'),d],check=True)
 assert (Path(d)/'src/lib.rs').read_bytes()==stepSource.read_bytes()
 assert json.loads((Path(d)/'source-cut.json').read_text())==stepCut
# Whole-copy leaf contracts and exact complete owned-parent composition.
for tag,folder,generator in [
 ('sdk-finish-fixed-frame-join-v3','sdk-finish-fixed-frame-v3','prepare-sdk-finish-fixed-frame.py'),
 ('sdk-finish-fixed-frame-join-v4','sdk-finish-fixed-frame-v4','prepare-sdk-finish-fixed-frame.py'),
 ('sdk-finish-fixed-frame-join-v5','sdk-finish-fixed-frame-v5','prepare-sdk-finish-fixed-frame.py'),
 ('sdk-std-copy-frame-join-v1','sdk-std-copy-frame-v1','prepare-sdk-std-copy-frame.py'),
 ('sdk-std-copy-bridge-join-v1','sdk-std-copy-frame-v1','prepare-sdk-std-copy-frame.py')]:
 source,cut,rp=checked(tag,folder,(3,4) if tag.endswith('fixed-frame-join-v5') else None)
 with tempfile.TemporaryDirectory() as d:
  subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021'/generator),d]+(['all-reply-lengths','bool-outcome'] if tag.endswith('fixed-frame-join-v5') else ['all-reply-lengths'] if tag.endswith('fixed-frame-join-v4') else []),check=True)
  assert (Path(d)/'src/lib.rs').read_bytes()==source.read_bytes()
  assert json.loads((Path(d)/'source-cut.json').read_text())==cut
 accepted[tag]['qualification']=cut['qualification']+' Specialized leaf/bridge only; no enclosing native caller instance.'
 if 'fixed-frame' in tag:
  version=tag.rsplit('-',1)[1]
  audit=json.loads((E/('receipts/sdk-finish-fixed-frame-properties-'+version+'/property-audit.json')).read_text())
  pins=json.loads((E/('sdk-finish-fixed-frame-properties-'+version+'-input.json')).read_text())
  assert audit['source_sha256']==pins['source_sha256']==sha(source)
  assert audit['proof_receipt_sha256']==pins['proof_receipt_sha256']==sha(rp)
  assert audit['program_sha256']==pins['program_sha256']
  assert any(p['class']=='assigns' for p in audit['selected_properties'])
  assert any('expected' in p['description'] for p in audit['selected_properties'])
  if version=='v5':
   covers=[p for p in audit['selected_properties'] if p['class']=='cover']
   assert len(covers)==4
   assert sum(p['description']=='fixed-size native whole copy first byte' for p in covers)==2
   assert 'Err(_)=>panic!' in source.read_text() and 'match native_finish(' in source.read_text()
   accepted[tag]['covers_total']=4
   accepted[tag]['cover_qualification']='3/4 aggregate; compiler duplicates the first-byte cover location. No per-location reachability or all-covers claim. All883 assertions passed; v4 independently checks the full-ProgramError block and all three original cover intentions.'
 if tag=='sdk-std-copy-frame-join-v1':
  audit=json.loads((E/'receipts/sdk-std-copy-frame-properties-v1/property-audit.json').read_text())
  pins=json.loads((E/'sdk-std-copy-frame-properties-v1-input.json').read_text())
  assert audit['source_sha256']==pins['source_sha256']==sha(source)
  assert audit['proof_receipt_sha256']==pins['proof_receipt_sha256']==sha(rp)
  assert audit['program_sha256']==pins['program_sha256']
  assert any(p['class']=='assigns' and p['name']=='memcpy.assigns.2' and 'array_replace' in p['description'] for p in audit['selected_properties'])
  assert any('expected()' in p['description'] for p in audit['selected_properties'])
 if 'bridge' in tag:
  command=json.loads(rp.read_text())['command']
  assert 'function-contracts' in command and 'stubbing' in command
  assert '#[kani::stub_verified(verified_byte_copy)]' in source.read_text()
copy=E/'sources/owned-sdk-copy-v1'
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'src'
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-owned-sdk-copy.py'),str(out)],check=True)
 assert (out/'src/lib.rs').read_bytes()==(copy/'src/lib.rs').read_bytes()
 assert json.loads((out/'source-cut.json').read_text())==json.loads((copy/'source-cut.json').read_text())
 i=Path(d)/'raw';i.mkdir();o=Path(d)/'adapt'
 for p in (copy/'generated/AspisS2SdkCopyReference').glob('*.lean.txt'):(i/p.name[:-4]).write_bytes(p.read_bytes())
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/adapt-owned-sdk-copy.py'),str(i),str(o)],check=True)
 for p in o.iterdir():assert p.read_bytes()==(S/p.name).read_bytes(),p
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/make-sdk-copy-parent.py'),str(o)],check=True)
 assert (o/'S2SdkCopyParentV1.lean').read_bytes()==(S/'S2SdkCopyParentV1.lean').read_bytes()
for phase in ['charon','aeneas']:
 r=json.loads((E/'receipts'/('owned-sdk-copy-v1-'+phase)/'receipt.json').read_text())
 inp=json.loads((copy/(phase+'-input.json')).read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert inp['source_sha256']==sha(copy/'src/lib.rs') and inp['tool_pins']
 assert inp['owned_sdk_dependency_sha256']==sha(B/'evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/src/lib.rs')

snap=E/'sources/owned-sdk-snapshots-v1'
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'src';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-snapshot-reference.py'),str(out)],check=True)
 assert (out/'src/lib.rs').read_bytes()==(snap/'src/lib.rs').read_bytes()
 i=Path(d)/'raw';i.mkdir();o=Path(d)/'adapt'
 for p in (snap/'generated/AspisS2SdkSnapshots').glob('*.lean.txt'):(i/p.name[:-4]).write_bytes(p.read_bytes())
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/adapt-sdk-snapshot.py'),str(i),str(o)],check=True)
 for p in o.iterdir():assert p.read_bytes()==(S/p.name).read_bytes(),p
for phase in ['charon','aeneas']:
 r=json.loads((E/'receipts'/('owned-sdk-snapshots-v1-'+phase)/'receipt.json').read_text())
 inp=json.loads((snap/(phase+'-input.json')).read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert inp['source_sha256']==sha(snap/'src/lib.rs') and inp['tool_pins']
borrowed=E/'sources/owned-sdk-borrowed-v1'
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'src';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-owned-sdk-borrowed.py'),str(out)],check=True)
 assert (out/'src/lib.rs').read_bytes()==(borrowed/'src/lib.rs').read_bytes()
 i=Path(d)/'raw';i.mkdir();o=Path(d)/'adapt'
 for p in (borrowed/'generated/AspisS2SdkOwned').glob('*.lean.txt'):(i/p.name[:-4]).write_bytes(p.read_bytes())
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/adapt-sdk-borrowed.py'),str(i),str(o)],check=True)
 for p in o.iterdir():assert p.read_bytes()==(S/p.name).read_bytes(),p
for phase in ['charon','aeneas']:
 r=json.loads((E/'receipts'/('owned-sdk-borrowed-v1-'+phase)/'receipt.json').read_text())
 inp=json.loads((borrowed/(phase+'-input.json')).read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert inp['source_sha256']==sha(borrowed/'src/lib.rs') and inp['tool_pins']

assert all(not p['has_errors'] for p in json.loads((E/'llbc-pins.json').read_text()))
flags=[json.loads(p.read_text())['rustflags'] for p in (E/'compiler-flags').glob('*/*.json')]
assert flags and all('opt-level=3' in r and 'overflow-checks=yes' in r and '--kani-compiler' in r for r in flags)
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.o','.a','.so','.dylib','.llbc','.bc','.out']
(E/'accepted-cuts.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='Checked finite SDK operation/lifecycle domains and exact pure snapshot adaptation. Reached phase cuts are explicit. Complete actual stage1 child instances and ordered caller join remain open; timed-out/context/codegen/preflight evidence is excluded from accepted cuts.',cuts=accepted),indent=2)+'\n')
print('PASS seventeen SDK cuts and complete owned-parent copy-loop adaptation; enclosing native caller joins remain open')
