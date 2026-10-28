from KND_driver import *
ROWS=json.loads((E/'KND_SCHEDULE.json').read_text())
BASE="#![feature(allocator_api)]\nextern crate alloc;\nmod KMX_stubs;\n"
ATTR="""#[kani::proof] #[kani::unwind(1770)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
"""
def source(row,negative):
 n,c,s=row['len'],row['cap'],row['size']
 return BASE+ATTR+f"""fn KND_transition() {{
 let initial:[u8;{n}]=kani::any(); let bytes:[u8;{s}]=kani::any();
 let mut out=alloc::vec::Vec::with_capacity({c});
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial);
 assert_eq!(out.len(),{n});assert_eq!(out.capacity(),{c});
 KMX_stubs::KMX_extend_from_slice(&mut out,&bytes);
 assert_eq!(out.len(),{n+s});assert_eq!(out.capacity(),{c});
 for j in 0..{n+s} {{
  assert_eq!(out[j],(if j<{n}{{initial[j]}}else{{bytes[j-{n}]}}) ^ {int(negative)}u8);
 }}
}}
"""
def main():
 # All wide and query transitions first; remaining budget covers 11 scalars.
 selected=[r for r in ROWS if r['size'] in [32,4]]
 selected += [r for r in ROWS if r['size']==16][-11:]
 assert len(selected)==45
 (E/'KND_SELECTED.json').write_text(json.dumps(selected,indent=2)+'\n')
 pairs=[]
 for i,row in enumerate(selected):
  statuses=[]
  for negative in [False,True]:
   a=f'KND_K{2*i+1+int(negative):03}'
   if (E/a/'classification.json').exists():
    statuses.append(json.loads((E/a/'classification.json').read_text())['result']);continue
   cfg=json.loads((E.parent/'kani-reverify3-20261028/KNA_K001.json').read_text())
   cfg.update(sources=['KND_windows.rs','KMX_stubs.rs','KMY_src/Cargo.lock','KND_gate.py'],command=['python3','KND_gate.py',a,'KND_transition'],negative_control=negative,transition=row,parent_gate=f'KND_K{2*i+1:03}',expected_time='optimized codegen then concrete append transition CBMC')
   statuses.append(run(a,cfg,source(row,negative)))
   if statuses[-1]=='ERROR':raise SystemExit('Inspect '+a)
  pairs.append(dict(transition=row,positive=statuses[0],control=statuses[1],positive_id=f'KND_K{2*i+1:03}',control_id=f'KND_K{2*i+2:03}',credit=statuses==['PASS','COUNTEREXAMPLE']))
  (E/'KND_PAIRS.json').write_text(json.dumps(pairs,indent=2)+'\n')
  if statuses[0]=='COUNTEREXAMPLE' or statuses[1]=='PASS':raise SystemExit('FIRST positive failure or passing control')
if __name__=='__main__':main()
