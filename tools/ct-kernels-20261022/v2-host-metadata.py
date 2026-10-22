#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,json,hashlib,platform
R=Path(__file__).resolve().parents[2];H=R.parent
subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/run-host.py'),'v2-feature-closure','cargo','tree','-p','aspis-r1-cost-probe','--features','optimized-terminal,ct-host-prover','-e','features','-i','aspis-core','--locked'],cwd=R,env=dict(os.environ,CT_EXPECTED='Read-only resolved Cargo feature closure; no compilation, proof generation or elimination'),check=True)
feature_log=(R/'receipts/v2-feature-closure/stdout.log').read_text()
assert 'aspis-core feature "ct-host-prover"' in feature_log
binary=H/'native-artifacts/v2'
symbols=subprocess.check_output(['nm','-C',str(binary)],text=True)
found=[line for line in symbols.splitlines() if 'aspis_r1_cost_probe::trace::VALUES' in line or 'aspis_r1_cost_probe::prover::CHECK_TIMES' in line]
assert not found,found
keys=[]
for p in sorted((H/'artifacts').glob('v2final-*/*keypair.json')):
 assert p.stat().st_mode&0o777==0o600
 keys.append(dict(path=str(p),mode='0600',retained=True))
assert len(keys)==3
metadata=dict(native_binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),tls_values_and_check_times_symbols_absent=True,core_ct_feature_resolved=True,statement_core_feature_note='Cargo unifies the single aspis-core package shared by aspis-statement and the host prover; compressor source unchanged',platform=platform.platform(),rustc=subprocess.check_output(['rustc','-Vv'],text=True),cargo=subprocess.check_output(['cargo','-V'],text=True),retained_build_keys=keys,source_revision=(R/'source-revision.txt').read_text().strip(),print_axioms='N/A; no Lean')
(R/'v2-host-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps(metadata,indent=2))
