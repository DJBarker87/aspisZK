from pathlib import Path
import json,hashlib,re
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019');b=Path('/home/dombarker/project-offloads/aspis-r1-worker-b-1h-native-20261019');i=Path('/home/dombarker/project-offloads/aspis-r1-worker-b-1h-injection-20261019');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(w/'runs/c1-codec/stdout.log')==sha(b/'baselines/codec1233.stdout.log')
a=json.loads((w/'candidate1-ordered.json').read_text());z=json.loads((b/'ordered-counter-no-prover.json').read_text());print('counter keys',list(a));
for d in [a,z]: d['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x:x['input_hex'])
for k in a:
 if 'revision' not in k:assert a[k]==z[k],k
assert '23 passed; 0 failed' in (w/'runs/c1-checkpoint/stdout.log').read_text()
for label,oldlabel in [('default-harness-fix','default'),('detail','detail')]:
 out=(w/('runs/c1-injections-'+label)/'stdout.log').read_text();assert '3 passed; 0 failed' in out
 base=(i/('runs/injection-no-prover-1h-'+oldlabel)/'stdout.log').read_text()
 # Exact emitted JSON/event records, excluding test-run timings.
 records=lambda s:[x[x.index('{'):] for x in s.splitlines() if '{' in x]
 assert records(out)==records(base),(label,len(records(out)),len(records(base)))
report={'codec_sha256':sha(w/'runs/c1-codec/stdout.log'),'codec_outputs':1233,'ordered_trace_identical':True,'counts':[349,234],'checkpoint23':True,'injections_default_and_detail_exact_records_match_baseline':True,'retained_failed_attempt':'c1-injections-default: missing baseline before_prepare test hook; corrected harness only','no_prover':True}
(w/'candidate1-native-validation.json').write_text(json.dumps(report,indent=2)+'\n')
env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR':'/home/dombarker/project-offloads/aspis-r1-decision1h-20261019/sbf-target','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true'}
plan={'command':['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(w/'sbf/programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',str(w/'candidate1-artifacts'),'--features','pool-adapter,private-leaf-salts','--skip-tools-install','--offline','-j','1','--','--locked'],'cwd':str(w/'sbf'),'source_revision':'3ab4faf7f5b488a0c82720717656a0ebf4c46efa','features':['pool-adapter','private-leaf-salts'],'out':str(w/'runs/c1-sbf'),'env':env,'expected_time':'SBF compilation/link only; no proof generation; reuse pinned 1h target cache'}
(w/'sbf.json').write_text(json.dumps(plan,indent=2)+'\n')
