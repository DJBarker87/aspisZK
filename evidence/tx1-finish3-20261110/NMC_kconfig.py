from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-tx1-finish3-20261110'
a,harness=sys.argv[1:3];only=len(sys.argv)>3 and sys.argv[3]=='codegen'
assert 1<=int(a[-3:])<=40
native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMC_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NMC_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse']
if only:native+=['--only-codegen']
x=dict(attempt=a,kind='kani',module=harness,sources=['NMC_gate.py','NMC_SOURCE_PINS.json','NMC_FROZEN_FILE_PINS.json','NMC_BASE_EXPECTED.json'],command=['python3','NMC_gate.py',a+'.json'],env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=B+'/NMC_target',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1',TMPDIR=B+'/NMC_tmp'),timeout=180,expected_time='Optimized compilation/codegen only' if only else 'Warm optimized compile then '+harness+' CBMC window; no field multiplication or SHA',root_package='aspis-r1-cost-probe-program',metadata_features='aspis-r1-cost-probe-program/pool-adapter,aspis-r1-cost-probe-program/private-leaf-salts',native_command=native,codegen_only=only,collect=[a+s for s in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json','-baseline-check.json']])
(E/(a+'.json')).write_text(json.dumps(x))
