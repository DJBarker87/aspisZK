from KND_driver import *
for i,which in enumerate(['schedule','queries','checksum','selected','arbitrary_lengths'],1):
 a=f'KND_R{i:03}'
 assert not (E/a/'receipt.json').exists()
 cfg=json.loads((E.parent/'kani-reverify3-20261028/KNA_R001.json').read_text())
 cfg.update(sources=['KND_native.rs','KND_native_gate.py','KMX_stubs.rs','KMY_src/Cargo.lock'],command=['python3','KND_native_gate.py',a,which],expected_time='optimized rustc compilation then concrete '+which+' comparisons; no elimination')
 assert run(a,cfg,(E/'KND_native.rs').read_text())=='PASS'
