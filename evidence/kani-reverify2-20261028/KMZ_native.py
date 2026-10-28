from KMZ_driver import *
for i,witness in enumerate(['expand','local','wide','limb','scalar'],1):
 a=f'KMZ_R{i:03}'
 if (E/a/'receipt.json').exists():continue
 cfg=json.loads((OLD/'KMY_K011.json').read_text());cfg.update(kind='rust',sources=['KMZ_native.rs','KMZ_native_gate.py','KMX_stubs.rs','KMY_field.rs','KMY_wide_exact.rs','KMY_src/Cargo.lock'],command=['python3','KMZ_native_gate.py',a,witness],negative_control_witness=True,expected_time='optimized rustc compile and concrete control witness replay; no elimination',note='Chosen all-zero concrete witnesses for the early byte controls; later controls retain solver-generated concrete playback values. Native allocation uses its allocator, so this corroborates a witness rather than replacing the Kani stubbed heap proof.')
 cfg['env']['RUSTC_BOOTSTRAP']='1'
 assert run(a,cfg,(OLD/'KMY_windows.rs').read_text())=='PASS'
