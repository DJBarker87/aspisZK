#!/usr/bin/env python3
"""Build/check evidence pins; never executes Lean, Rust, or extraction."""
from pathlib import Path
import hashlib,json,re,sys
E=Path(__file__).resolve().parent
ROOT=E.parents[4]; B=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
pins=read(E/'input-hashes.json')
assert all(sha(ROOT/p)==h for p,h in pins.items()),'Production input drift'
remote=read(E/'source-validation.json')
assert remote['checked_files']==len(pins)==487 and not remote['mismatches']
assert set(remote['test_only_instrumented_files'])=={'programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/pair_forest_dispatch.rs'}
for n in ['Types','Funs']:
 assert (B/'lean/AspisR20Pool'/f'{n}.lean').read_bytes()==(E/'extraction-strip-v2/generated/AspisR20Pool'/f'{n}.lean').read_bytes()
final=['withdrawal-prerequisite-v1','statement-v2','strip-types-v1','strip-funs-v1','strip-proof-v5']
accepted=[]
for name in final:
 r=read(E/'proofs'/name/'receipt.json'); assert r['exit_status']==0 and r['swaps']==0
 src=B/'lean'/(r['module'].replace('.','/')+'.lean')
 assert sha(src)==r['source_sha256'] and src.read_bytes()==(E/'proofs'/name/'source.lean').read_bytes()
 assert len(re.findall(r'^#print axioms',src.read_text(),re.M))==len(r['print_axioms'])
 for report in r['print_axioms']:
  m=re.search(r'\[([^\]]*)\]',report,re.S)
  assert m and {x.strip() for x in m[1].split(',')}<={'propext','Classical.choice','Quot.sound'},report
 accepted.append(dict(attempt=name,**r))
rust=read(E/'receipts/pool-lib-tests/receipt.json')
assert rust['exit_status']==0 and rust['swaps']==0
assert rust['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
log=(E/'receipts/pool-lib-tests/stdout.log').read_text()
assert '119 passed; 0 failed; 0 ignored' in log
for n in ['r20_hint_reorder_variant_and_stale_request_reject_before_cpi','r20_strip_reencode_is_exact_for_both_payment_variants','r20_cpi_exact_bytes_and_order']:
 assert n+' ... ok' in log
finalrust=read(E/'receipts/pool-r20-tests-v2/receipt.json')
assert finalrust['exit_status']==0 and finalrust['swaps']==0
assert '3 passed; 0 failed; 0 ignored' in (E/'receipts/pool-r20-tests-v2/stdout.log').read_text()
release=read(E/'receipts/pool-release-features-v3/receipt.json')
assert release['exit_status']==0 and release['swaps']==0
assert release['command'][release['command'].index('--features')+1]=='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit'
assert '121 passed; 0 failed; 0 ignored' in (E/'receipts/pool-release-features-v3/stdout.log').read_text()
for row in read(E/'frozen-source-check.json')['files']:
 assert sha(ROOT/row['path'])==row['sha256'] and row['equal_to_frozen']
for p in E.glob('reservation*.json'):
 r=read(p);assert r['all_populated_scopes_bounded'] and r['bounded_reserved_bytes']+8*2**30<=r['safe_limit_bytes']
for p in E.glob('receipts/*/receipt.json'):
 r=read(p);assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'
assert read(E/'receipts/r20-encoder-v2-aeneas/receipt.json')['exit_status']==2
assert 'lines 442:18-448:9' in (E/'receipts/r20-encoder-v2-aeneas/stderr.log').read_text()
for p in (B/'lean/AspisR20Pool').glob('*.lean'):
 assert not re.search(r'^\s*(?:axiom|opaque)\b',p.read_text(),re.M)
for p in [B/'lean/R20PoolHintStrip.lean',B/'lean/R20PoolStatementAgreement.lean']:
 assert not re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',p.read_text())
assert all(not p.name.endswith(('.olean','.llbc','.tar.gz')) for p in E.rglob('*') if p.is_file())
assets={str(p.relative_to(E)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(E.rglob('*')) if p.is_file() and p.name!='manifest.json'}
design={p.name:sha(p) for p in [B/'design/R20-POOL-HANDOFF-AUDIT-20261020.md',B/'design/R20-POOL-HANDOFF-20261020.md']}
result=dict(schema='focused-extractor-proof-packet-v1',source_revision=rust['source_revision'],scope='R20 exact extracted suffix stripping; conditional retained-adapter statement equality; account and ASQ8 encoder source audit; native tests. R20/P2/R9 execution composition remains open.',accepted_lean=accepted,rust=rust,final_focused_rust=finalrust,release_feature_rust=release,design=design,assets=assets,source_inputs=len(pins),standard_axioms_only=True,request_encoder_extraction='Stopped: pinned Aeneas Unreachable at payment-variant borrow join',full_frozen_manifest_replayed=False)
if '--write' in sys.argv:(E/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
else: assert read(E/'manifest.json')==result,'Evidence manifest drift'
print(json.dumps(dict(accepted_lean=len(accepted),axiom_reports=sum(len(r['print_axioms']) for r in accepted),tests_passed=121,source_inputs=len(pins))))
