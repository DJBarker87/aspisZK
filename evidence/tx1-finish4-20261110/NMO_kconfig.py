from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-tx1-finish4-20261110'
a,harness=sys.argv[1:3];only=len(sys.argv)>3 and sys.argv[3]=='codegen'
assert 1<=int(a[-3:])<=100
native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMO_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NMO_target','--features','optimized-terminal,program-build,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse']
if only:native+=['--only-codegen']
x=dict(attempt=a,kind='kani',module=harness,sources=['NMO_gate.py','NMO_SOURCE_PINS.json','NMO_FROZEN_FILE_PINS.json','NMO_BASE_EXPECTED.json'],command=['python3','NMO_gate.py',a+'.json'],env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=B+'/NMO_target',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1',TMPDIR=B+'/NMO_tmp'),timeout=180,expected_time='Optimized compilation/codegen only' if only else 'Warm optimized compile then '+harness+' CBMC window; no field multiplication or SHA',root_package='aspis-r1-cost-probe',metadata_features='aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build,aspis-r1-cost-probe/private-leaf-salts',native_command=native,codegen_only=only,collect=[a+s for s in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json','-baseline-check.json']])
(E/(a+'.json')).write_text(json.dumps(x))
