from NJN_native import *
base=(E/'NJN_sdk.rs.txt').read_text()
a=base.index(' let held:usize=kani::any();');b=base.index(' assert_eq!(counter(&a),0);',a)+len(' assert_eq!(counter(&a),0);')
builder=''' let held:usize=NJN_PRECOUNT;
 let pre=held as isize;
'''
for k in range(7):builder+=f' let g{k}=if held>{k} {{Some(a.try_borrow_data().unwrap())}}else{{None}};\n'
builder+=' assert_eq!(counter(&a),pre);\n ($body)(&a,pre,p);\n'
for k in range(7):builder+=f' drop(g{k});\n'
builder+=' assert_eq!(counter(&a),0);'
base=base[:a]+builder+base[b:]
(E/'NJN_sdk_split.rs.txt').write_text(base)
# Each count is a different safely constructed native pre-state; original target
# names retained. The array/whole-carrier-copy shape that timed out is removed.
i=25
for n in range(8):
 s=base.replace('NJN_PRECOUNT',str(n))
 for h in ['shared_contract','shared_counter_control','shared_cell_control','exclusive_contract','exclusive_cell_control']:
  assert i<=64
  r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
  log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
  if 'timed out' in log or 'VERIFICATION' not in log:raise SystemExit('split packet stopped; review before next shape')
  i+=1
