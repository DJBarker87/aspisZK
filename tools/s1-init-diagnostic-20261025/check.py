#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-init-diagnostic-20261025';m=json.loads((P/'plan.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['status']=='PREPARED_NOT_RUN' and not m['compiler_or_solver_launched'] and m['host_operations_performed']==0 and not m['native_initializedness_proved'] and m['exit_status'] is None
assert sha(E/m['basis_receipt'])==m['basis_receipt_sha256'] and sha(E/m['basis_input'])==m['basis_input_sha256']
old=json.loads((E/m['basis_receipt']).read_text());cmd=old['command'].copy();cmd.insert(2,'--only-codegen');assert cmd==m['command'] and m['planned_limits']['MemorySwapMax']==0
for row in m['upstream']:
 p=P/'upstream'/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
args=(P/'upstream/kani-driver/src/args/mod.rs').read_text();assert 'Kani will only compile the crate. No verification will be performed' in args and 'pub only_codegen: bool' in args
session=(P/'upstream/kani-compiler/src/session.rs').read_text();assert 'const LOG_ENV_VAR: &str = "KANI_LOG"' in session and 'EnvFilter::from_env(LOG_ENV_VAR)' in session
uninit=(P/'upstream/kani-compiler/src/kani_middle/transform/check_uninit/ptr_uninit/mod.rs').read_text();assert uninit.index('trace!(function=?instance.name(), "transform")')<uninit.index('UninitInstrumenter::run(')
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',kind='prepared-source-only-compiler-diagnostic',host_operations=0,compiler_or_solver_launched=False,native_initializedness_proved=False)))
