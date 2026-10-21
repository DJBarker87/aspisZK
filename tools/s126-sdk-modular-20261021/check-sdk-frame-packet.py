#!/usr/bin/env python3
"""Audit concrete SDK write-frame evidence, without claiming parent closure."""
from pathlib import Path
import hashlib,json,re,tomllib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={}
for mode,method in [('shared','try_borrow_data'),('exclusive','try_borrow_mut_data')]:
 name='sdk-'+mode+'-write-frame-v2';folder=E/'sources'/name
 source=folder/'src/lib.rs';text=source.read_text()
 cut=json.loads((folder/'source-cut.json').read_text());assert cut['source_sha256']==sha(source)
 assert 'Both data and lamport Rc strong counts1..isizeMAX' in cut['rc_counter_domain']
 inp=json.loads((E/(name+'-input.json')).read_text());assert inp['source_sha256']==sha(source)
 assert inp['env']['RUSTFLAGS'].startswith('-C opt-level=3 ')
 assert inp['env']['CARGO_BUILD_JOBS']=='1' and inp['env']['CARGO_NET_OFFLINE']=='true'
 assert inp['tool_pins']
 assert '#[kani::modifies(counter.cast::<isize>())]' in text
 assert '#[kani::proof_for_contract('+mode+'_roundtrip)]' in text
 assert 'match account.'+method+'() {' in text
 assert 'old(unsafe{(*counter).get()})' in text
 packages={p['name']:p for p in tomllib.loads((folder/'Cargo.lock').read_text())['package']}
 for package,version in [('solana-program','2.3.0'),('solana-account-info','2.3.0'),('solana-program-error','2.2.2')]:
  assert packages[package]['version']==version and packages[package]['checksum']
 receipt=E/'receipts'/name/'receipt.json';r=json.loads(receipt.read_text())
 assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
 assert 'function-contracts' in r['command'] and '--unwinding-assertions' in r['command']
 log=(receipt.parent/'stdout.log').read_text()
 failures=re.search(r'0 of (\d+) failed',log);assert failures and '2 of 2 cover properties satisfied' in log
 pins=json.loads((E/('sdk-'+mode+'-properties-v2-input.json')).read_text())
 audit=json.loads((E/'receipts'/('sdk-'+mode+'-write-properties-v2')/'property-audit.json').read_text())
 assert pins['checked_receipt_sha256']==sha(receipt)
 assert pins['checked_source_sha256']==sha(source)==audit['source_sha256']
 assert pins['program_sha256']==audit['checked_program_sha256']
 props=audit['contract_properties']
 assigns=[p for p in props if p['class']=='assigns'];assert assigns
 assert any('replace::<isize>' in p['name'] for p in assigns)
 assert any('AccountInfo' in p['name'] and method in p['name'] for p in assigns)
 assert any(p['class']=='assertion' and 'old(' in p['description'] and 'counter' in p['description'] for p in props)
 accepted[mode]=dict(source_sha256=sha(source),receipt_sha256=sha(receipt),checked_program_sha256=pins['program_sha256'],assertions=int(failures[1]),covers=2,assigns_properties=len(assigns),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'])
for p in json.loads((E/'std/kani-contract-source-pins.json').read_text()):
 assert sha(E/'std'/p['export'])==p['sha256']
flags=[json.loads(p.read_text())['rustflags'] for p in (E/'compiler-flags').glob('*/*.json')]
assert flags and all('opt-level=3' in row and 'overflow-checks=yes' in row and '--kani-compiler' in row for row in flags)
libraries=json.loads((E/'std/kani-library-pins.json').read_text());assert libraries and any(p['path'].endswith('/libstd.rlib') for p in libraries)
assert all(len(p['sha256'])==64 and p['bytes']>0 for p in libraries)
(E/'accepted-sdk-write-frames.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='Concrete pinned SDK acquire/drop write-set and counter-restoration checks, finite storage/view domain0..58295, every signed counter and all safe Rc header counts. Native compiler/layout and Kani function-contract trust boundaries explicit. No complete SDK stage1 correspondence or release claim.',steps=accepted),indent=2)+'\n')
print('PASS concrete SDK shared/exclusive write-set checks, contract assign/postcondition metadata, frozen dependency versions, source/tool/resource pins; no parent closure')
