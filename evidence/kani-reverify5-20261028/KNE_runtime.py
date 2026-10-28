from KNE_driver import *
ROWS=json.loads((E.parent/'kani-reverify4-20261028/KND_REMAINING_RUNTIME.json').read_text())
BASE='#![feature(allocator_api)]\nextern crate alloc;\nmod KMX_stubs;\n'
ATTR='''#[kani::proof] #[kani::unwind(1770)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
'''
def source(row,lo,hi,negative):
 n,c,s=row['len'],row['cap'],row['size']
 return BASE+ATTR+f'''fn KND_transition() {{
 let initial:[u8;{c}]=kani::any(); let bytes:[u8;{s}]=kani::any();
 let mut out=alloc::vec::Vec::from(initial);out.truncate({n});
 assert_eq!(out.len(),{n});assert_eq!(out.capacity(),{c});
 KMX_stubs::KMX_extend_from_slice(&mut out,&bytes);
 assert_eq!(out.len(),{n+s});assert_eq!(out.capacity(),{c});
 for j in {lo}..{hi} {{
  assert_eq!(out[j],(if j<{n}{{initial[j]}}else{{bytes[j-{n}]}}) ^ {int(negative)}u8);
 }}
}}
'''
def main():
 unique={(r['len'],r['cap'],r['size']) for r in ROWS};assert len(unique)==len(ROWS)==73
 jobs=[]
 for row in ROWS:
  n,s=row['len'],row['size']
  windows=[(0,n),(n,n+s)] if row['operation'] in ['checksum','weight53'] else [(0,n+s)]
  for lo,hi in windows:jobs.append((row,lo,hi))
 assert len(jobs)==75
 pairs=[]
 for i,(row,lo,hi) in enumerate(jobs):
  statuses=[]
  for neg in [False,True]:
   a=f'KNE_K{2*i+1+int(neg):03}'
   if (E/a/'classification.json').exists():
    statuses.append(json.loads((E/a/'classification.json').read_text())['result']);continue
   cfg=json.loads((E.parent/'kani-reverify3-20261028/KNA_K001.json').read_text())
   cfg.update(sources=['KNE_windows.rs','KMX_stubs.rs','KMY_src/Cargo.lock','KNE_gate.py'],command=['python3','KNE_gate.py',a,'KND_transition'],negative_control=neg,transition=row,index_window=[lo,hi],parent_gate=f'KNE_K{2*i+1:03}',expected_time='optimized codegen then fixed-capacity append and concrete observation window CBMC')
   statuses.append(run(a,cfg,source(row,lo,hi,neg)))
   if statuses[-1]=='ERROR':raise SystemExit('Inspect '+a)
  pairs.append(dict(transition=row,index_window=[lo,hi],positive=statuses[0],control=statuses[1],positive_id=f'KNE_K{2*i+1:03}',control_id=f'KNE_K{2*i+2:03}',credit=statuses==['PASS','COUNTEREXAMPLE']))
  (E/'KNE_PAIRS.json').write_text(json.dumps(pairs,indent=2)+'\n')
  if statuses[0]=='COUNTEREXAMPLE' or statuses[1]=='PASS':raise SystemExit('FIRST positive failure or passing control')
if __name__=='__main__':main()
