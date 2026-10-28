from KNA_driver import *
for i,witness in enumerate(['query','body','selected','append16','append32and4'],1):
 a=f'KNA_R{i:03}'
 if (E/a/'receipt.json').exists():continue
 cfg=json.loads((OLD/'KMY_K011.json').read_text())
 cfg.update(kind='rust',sources=['KNA_native.rs','KNA_native_gate.py','KMX_stubs.rs','KMY_field.rs','KMY_wide_exact.rs','KMY_src/Cargo.lock'],command=['python3','KNA_native_gate.py',a,witness],negative_control_witness=True,expected_time='optimized rustc compilation then concrete '+witness+' comparisons; no elimination',note='Native corroboration only. It does not replace symbolic Kani heap gates; native Vec uses native allocator internals. The body case separately invokes the unchanged KMX_realloc on initialized bytes.')
 cfg['env']['RUSTC_BOOTSTRAP']='1'
 assert run(a,cfg,(E/'KNA_native.rs').read_text())=='PASS'
