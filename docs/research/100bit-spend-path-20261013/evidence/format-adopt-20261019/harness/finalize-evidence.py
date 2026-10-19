#!/usr/bin/env python3
"""Collect pins and validate adopted artifacts without rerunning full regressions."""
import hashlib,json,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019')
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((H/'source-hashes.json').read_text())
for f in source['files']: assert sha(H/'src'/f['path'])==f['sha256'],f['path']
cu=json.loads((H/'cu.json').read_text())
assert cu['all_stage1_ok'] and cu['all_settlement_ok']
for r in cu['rows']:
    ev=json.loads((H/'runs/verified'/('reuse-'+r['fixture'])/'evidence.json').read_text())['execution']
    assert ev['outcome']=='accepted'
    assert [ev['stage1_compute_units'],ev['compute_units']]==[r['stage1_cu'],r['settlement_cu']]
scenarios=[]
for p in sorted((H/'runs/verified').glob('*/evidence.json')):
    e=json.loads(p.read_text())['execution']; label=p.parent.name
    if label.startswith(('reuse-','prefund-rent-','replay-')): assert e['outcome']=='accepted',label
    else: assert e['outcome']=='rejected',label
    if label.startswith('replay-'): assert '1095966758' in e['replay']['error'],label
    scenarios.append(dict(scenario=label,outcome=e['outcome'],error=e['error'],replay_error=e['replay']['error'] if e.get('replay') else None,
        atomicity=json.loads(p.read_text()).get('atomicity')))
(H/'scenario-results.json').write_text(json.dumps(scenarios,indent=2)+'\n')
retry=json.loads((H/'runs/r1p-retry-gate.json').read_text())
assert retry['attempts']>=8 and retry['accepted']==retry['attempts'] and retry['accepted_proofs_verified_strict_and_dense']==retry['attempts']
assert retry['retry_loop']['verified_strict_and_dense']
for kind in ['verifier','pool']:
    assert json.loads((H/'stack'/kind/'stack-audit.json').read_text())['gate_pass']
programs=[('verifier','aspis_r1_cost_probe_program.so','pool-adapter,private-leaf-salts (dependency: optimized-terminal,program-build)'),('pool','aspis_pool.so','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit')]
pins=['Source revision: '+source['source_revision'],'Base revision: '+source['base_revision'],
      'SBF: solana-cargo-build-sbf 3.1.13; platform-tools v1.52; rustc 1.89.0-dev; LLVM 20.1.7; --offline --locked -j 4; release',
      'Native: rustc 1.94.1 (e408947bf 2026-03-25); cargo 1.94.1; --release --offline --locked -j 4',
      'Artifacts retained on build host only; no ELFs or signing keys committed.']
for kind,name,features in programs:
    pins.append('\n'+kind+' features: '+features)
    for filename in [name,'linked.elf']:
        p=H/'artifacts'/kind/filename
        pins.append(f'{sha(p)}  {p.stat().st_size} bytes  {p}')
pins.append('\nMeasurement driver: B1 source 747cf4df771819020942d2d9f793337092c7e0b2575706a99106160452cd30b2, patched by harness/patch_driver_adopt.py; features private-leaf-salts; native release')
for rel in ['src/tools/r1-cost-probe-adopt-driver/src/bin/pool_gate.rs','src/tools/r1-cost-probe-adopt-driver/Cargo.toml','src/tools/r1-cost-probe-adopt-driver/Cargo.lock','artifacts/pool_gate_adopt']:
    p=H/rel
    pins.append(f'{sha(p)}  {p.stat().st_size} bytes  {p}')
registry=Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')
pins.append(f'\nRegistry (B1 unchanged): {sha(registry)}  {registry.stat().st_size} bytes')
pins.append('\nChanged source hashes: source-hashes.json (all verified against host tree).')
(H/'artifacts-sha256.txt').write_text('\n'.join(pins)+'\n')
summary=[]
for p in sorted((H/'receipts').glob('*/receipt.json')):
    r=json.loads(p.read_text())
    summary.append(dict(run=p.parent.name,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],limits=r['limits']))
(H/'run-summary.json').write_text(json.dumps({'source_revision':source['source_revision'],'receipts':summary},indent=2)+'\n')
print('Source hashes verified:',len(source['files']),'; fixtures: 6; scenarios:',len(scenarios),'; retry:',retry['accepted'],'/',retry['attempts'],'; both stack audits passed')
