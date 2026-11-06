from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-field4-20261108'
a,target,*flags=sys.argv[1:]
s=(E.parent/'slice-d-field3-20261105/NGH_gate.py').read_text().replace('NGH_','NKJ_')
s=s.replace("pins=json.loads((B/'NKJ_SOURCE_PINS.json').read_text())", """# Install only this owned harness and validate every frozen file before EACH run.
(S/'crates/aspis-core/src/field/NKJ_segments.rs').write_text((B/'NKJ_segments.rs.txt').read_text())
frozen_pins=json.loads((B/'NKJ_FROZEN_PINS.json').read_text())
raw_inputs=json.loads(__import__('lzma').decompress((B/'NKJ_FROZEN.json.xz').read_bytes()))
lib='crates/aspis-core/src/lib.rs';libbase=__import__('base64').b64decode(raw_inputs[lib])
(S/lib).write_bytes(b'#![cfg_attr(kani, feature(allocator_api))]'+bytes([10])+libbase)
pins={n:h for n,h in frozen_pins.items() if n not in ['crates/aspis-core/src/field.rs',lib]}
assert (S/lib).read_bytes()==b'#![cfg_attr(kani, feature(allocator_api))]'+bytes([10])+libbase

base=__import__('base64').b64decode(json.loads(__import__('lzma').decompress((B/'NKJ_FROZEN.json.xz').read_bytes()))['crates/aspis-core/src/field.rs'])
assert (S/'crates/aspis-core/src/field.rs').read_bytes()==base+b'\\n#[cfg(kani)]\\nmod NKJ_segments;\\nmod NKJ_reference;\\n'
pins['crates/aspis-core/src/field/NKJ_reference.rs']=sha(B/'NKJ_reference.rs.txt')
pins['crates/aspis-core/src/field/NKJ_segments.rs']=sha(B/'NKJ_segments.rs.txt')
""")
(E/'NKJ_gate.py').write_text(s)
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NKJ_src/crates/aspis-core/Cargo.toml','--target-dir',B+'/NKJ_target','--features','r0','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
if flags and flags[0]!='invert':cmd+=['--solver',flags[0]]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKJ_tmp',CARGO_TARGET_DIR=B+'/NKJ_target',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKJ_invert' if 'invert' in flags else '')+(' --cfg NKJ_modifies_bad' if 'modifies_bad' in flags else ''))
cfg=dict(attempt=a,kind='kani',module=target,root_package='aspis-core',sources=['NKJ_gate.py','NKJ_segments.rs.txt','NKJ_reference.rs.txt','NKJ_src/crates/aspis-core/src/field.rs','NKJ_src/Cargo.lock'],upload=['NKJ_gate.py','NKJ_segments.rs.txt'],command=['python3','NKJ_gate.py',a+'.json'],native_command=cmd,collect=[a+'-graph-check.json',a+'-graph.stderr',a+'-lock-check.json',a+'-source-check.json'],env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='optimized compilation then named scalar source segment contract; no field multiplication',feature_parity='aspis-core/r0 equals core feature closure of deployed verifier; no verifier/program harness compiled')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2))
