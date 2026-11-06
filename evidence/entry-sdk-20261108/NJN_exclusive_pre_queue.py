from NJN_native import *
p=E/'NJN_K016/NJN_PRELAUNCH_STOP.txt'
if p.exists():p.rename(E/'NJN_PRELAUNCH_STOP.txt');p.parent.rmdir()
s=(E/'NJN_sdk_split.rs.txt').read_text().replace(' let held:usize=NJN_PRECOUNT;\n let pre=held as isize;',' let held:usize=0;\n let xguard=a.try_borrow_mut_data().unwrap();\n let pre:isize=-1;').replace(' assert_eq!(counter(&a),0);',' drop(xguard);\n assert_eq!(counter(&a),0);')
s=s.replace('let mut bytes=[kani::any::<u8>();2];let p=bytes.as_ptr();','let mut bytes=kani::vec::exact_vec::<u8,58295>();let p=bytes.as_ptr();let coord:usize=kani::any();kani::assume(coord<58295);let old=bytes[coord];').replace(',p,2)',',p,58295)').replace(' drop(xguard);',' assert_eq!(xguard[coord],old);\n drop(xguard);')
(E/'NJN_sdk_exclusive_pre.rs.txt').write_text(s)
for i,h in [(16,'shared_contract'),(17,'shared_cell_control'),(18,'exclusive_contract'),(69,'exclusive_cell_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log or (i in [16,18]) and r['exit_status']!=0:break
