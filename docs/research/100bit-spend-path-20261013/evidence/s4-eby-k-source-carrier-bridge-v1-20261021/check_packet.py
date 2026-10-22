#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256((P/p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok: raise SystemExit('FAIL: '+msg)
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items(): need(sha(rel)==h, f'hash mismatch: {rel}')
r=json.loads((P/'sources/rust-source-cuts.json').read_text())
b=(P/'sources/rust/fast_pairing.rs').read_bytes()
need(hashlib.sha256(b).hexdigest()==r['source_sha256'],'Rust source hash')
for cut in r['cuts']:
 got=b[cut['start_byte']:cut['end_byte_exclusive']]
 need(hashlib.sha256(got).hexdigest()==cut['sha256'],cut['name']+' slice hash')
 need(got.decode()==cut['text'],cut['name']+' slice text')
need(b'pub struct Dot { sums:[u64;4] }' in b,'Rust Dot field shape')
need(b'pub struct EbyKDot {\n    c0: canonical::Dot,\n    c1: canonical::Dot,\n    count: usize,\n}' in b,'Rust EbyKDot field shape')
# Confirm Lean declarations carry the exact field types and order.
t=(P/'sources/AspisR1EbyKFinish/Types.lean').read_text()
need('structure canonical.Dot where\n  sums : Array Std.U64 4#usize' in t,'source Dot Lean fields')
need('structure EbyKDot where\n  c0 : canonical.Dot\n  c1 : canonical.Dot\n  count : Std.Usize' in t,'source EbyKDot Lean fields')
t=(P/'sources/EbyKPushExplicitTypesV1.lean').read_text()
need('structure fast_pairing.canonical.Dot where\n  sums : Array Std.U64 4#usize' in t,'PairCut Dot Lean fields')
need('structure fast_pairing.EbyKDot where\n  c0 : fast_pairing.canonical.Dot\n  c1 : fast_pairing.canonical.Dot\n  count : Std.Usize' in t,'PairCut EbyKDot Lean fields')
rec=json.loads((P/'receipts/local-lean-run.json').read_text())
need(rec['exit_status']==0,'Lean target exit')
need(rec['source_revision_at_launch']==m['source_revision']['git_head_at_launch'],'launch revision mismatch')
need(rec['sha256']['/tmp/S4EbyKDotSourceCarrierBridgeV1.lean']==sha(P/'sources/S4EbyKDotSourceCarrierBridgeV1.lean'),'compiled source pin')
need(rec['sha256']['/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean']==m['compiler']['sha256'],'compiler pin')
need(m['axioms']==['propext','Classical.choice','Quot.sound'],'axiom receipt')
for mod,recfile in [('AspisR1EbyKFinish.Types','receipts/finish-types-receipt.json'),('EbyKPushExplicitTypesV1','receipts/s5-import-owner.json')]:
 owner=m['direct_import_source_map'][mod]
 need(sha(owner['source_path'])==owner['source_sha256'],mod+' source owner hash')
 need(owner['source_sha256']==json.loads((P/recfile).read_text()).get('source_sha256',owner['source_sha256']),mod+' producer source hash')
 producer=json.loads((P/recfile).read_text())
 selected=producer.get('selected_object_sha256',producer.get('object_sha256'))
 need(owner['object_sha256']==selected,mod+' producer object hash')
print('EbyK Dot source-carrier packet: PASS')
