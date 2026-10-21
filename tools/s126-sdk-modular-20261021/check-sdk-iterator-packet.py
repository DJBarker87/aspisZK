#!/usr/bin/env python3
"""Validate concrete next/constructor evidence; never imply complete SDK join."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
std=E/'std-any-source';sdk=E/'sdk-iterator-source'
pin=json.loads((std/'source-pins.json').read_text());assert pin['identical_any_method']
def cut(s,name,prefix='fn '):
 a=s.index(prefix+name);b=s.index('{',a)+1;i=b;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
for name in ['aeneas-rust-slice-iter-macros.rs','kani-rust-slice-iter-macros.rs']:
 method=cut((std/'std'/name).read_text(),'any<F>')
 assert method==pin['any_method'] and hashlib.sha256(method.encode()).hexdigest()==pin['any_method_sha256']
assert any(row['tag']=='std-any-v5' and not row['has_errors'] for row in pin['llbc'])
for phase in ['charon','aeneas']:
 row=json.loads((std/'std-any-v5/receipts'/phase/'receipt.json').read_text())
 assert row['exit_status']==0 and row['swaps']==0
 assert row['limits']['memory.swap.max']=='0' and row['limits']['memory.max']=='8589934592'
 if phase=='charon':assert '--sysroot' not in row['command']
# Validate native source bodies against the bodies that were actually extracted.
pins=json.loads((sdk/'source-pins.json').read_text())
for name,row in pins['functions'].items():
 for tag in ['sdk-iterator-reference-v1','sdk-iterator-reference-v2','sdk-iterator-reference-v3']:
  body=cut((sdk/tag/'src/lib.rs').read_text(),name,'pub fn ')
  assert body==row['source'] and hashlib.sha256(body.encode()).hexdigest()==row['sha256']
assert any(row['tag']=='sdk-iterator-reference-v2' and not row['has_errors'] for row in pins['llbc'])
for phase in ['charon','aeneas']:
 row=json.loads((sdk/'sdk-iterator-reference-v2/receipts'/phase/'receipt.json').read_text())
 assert row['exit_status']==0 and row['swaps']==0
 assert row['limits']['memory.swap.max']=='0'
native=sdk/'native-receipts';nativeTag='sdk-iterator-reference-join-v3'
r=json.loads((native/nativeTag/'receipt.json').read_text());i=json.loads((native/(nativeTag+'-input.json')).read_text())
assert r['exit_status']==0 and r['swaps']==0
assert r['limits']['memory.max']=='8589934592' and r['limits']['memory.swap.max']=='0'
assert '--unwinding-assertions' in r['command'] and '--solver' in r['command']
assert i['source_sha256']==sha(sdk/'sdk-iterator-reference-v3/src/lib.rs')
log=(native/nativeTag/'stdout.log').read_text()
assert re.search(r'0 of 1053 failed',log) and '3 of 3 cover properties satisfied' in log
flags=[]
for p in (sdk/'compiler-flags').rglob('*.json'):
 data=p.read_text()
 if 'opt-level=3' in data and 'overflow-checks=yes' in data and 'kani-compiler' in data:flags.append(str(p.relative_to(sdk)))
assert flags,'effective optimized Kani compiler flags missing'
for package,folder,adapter,module,metadata in [
 (std,'std-any-v5/generated/AspisS2StdAny','adapt-std-any.py','S2StdAnySourceV1.lean','std-any-emission-adapter.json'),
 (sdk,'sdk-iterator-reference-v2/generated/AspisS2SdkIterator','adapt-sdk-iterator.py','S2SdkSourceIteratorV1.lean','sdk-iterator-emission-adapter.json')]:
 with tempfile.TemporaryDirectory(prefix='s126-iterator-check-') as d:
  root=Path(d);raw=root/'raw';out=root/'out';raw.mkdir()
  for name in ['Types.lean','Funs.lean']:(raw/name).write_bytes((package/folder/(name+'.txt')).read_bytes())
  subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021'/adapter),str(raw),str(out)],check=True)
  assert (out/module).read_bytes()==(S/module).read_bytes()
  assert (out/metadata).read_bytes()==(S/metadata).read_bytes()
with tempfile.TemporaryDirectory(prefix='s126-native-parent-check-') as temp:
 subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/make-sdk-native-scan-parent.py'),temp],check=True)
 for f in ['S2SdkNativeScanParentV1.lean','sdk-native-scan-parent-fission.json']:
  assert (Path(temp)/f).read_bytes()==(S/f).read_bytes()
fission=json.loads((S/'sdk-native-scan-parent-fission.json').read_text())
assert len(fission['factored_blocks'])==2 and fission['emitted_model_sha256']==sha(S/'S2SdkOwnedModelV1.lean')
assert fission['source_sha256']==sha(S/'S2SdkNativeScanParentV1.lean')
(E/'accepted-sdk-iterator.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',native_receipt='sdk-iterator-source/native-receipts/'+nativeTag+'/receipt.json',native_source_sha256=i['source_sha256'],optimized_flag_records=flags,qualification='Concrete native constructor/one-step join plus exact full-MIR std any extraction and explicit SDK reference instantiation. The separately checked Lean parent theorem removes scan/iterator premises. Actual full AccountInfo heap/caller construction and ordered global join remain open.'),indent=2)+'\n')
print('PASS native SDK constructor/next join, exact extraction body reuse, optimized source/tool/resource pins, all source adaptations; no whole-SDK closure')
