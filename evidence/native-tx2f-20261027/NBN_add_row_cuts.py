from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NBN_more.rs.txt';old=p.read_text();assert 'fn NBN_rows_live_inside' not in old
s='\n// Split replacement for NBH dynamic-store timeouts: one observed byte, no old-array clone.\n'
for name,n,base in [('live',800,160),('after',688,48)]:
 for region in ['inside','before','after']:
  if region=='inside':
   obs='let offset:usize=kani::any();kani::assume(offset<32);let j=start+offset;'
   expect='bytes[offset]'
  elif region=='before':
   obs=f'let j:usize=kani::any();kani::assume(j<start);'
   expect='old'
  else:
   obs=f'let j:usize=kani::any();kani::assume(j>=start+32 && j<{n});'
   expect='old'
  s+=f'''#[kani::proof]
#[kani::unwind(1881)]
fn NBN_rows_{name}_{region}(){{
 let mut out:[u8;{n}]=kani::any();let bytes:[u8;32]=kani::any();
 let k:usize=kani::any();kani::assume(k<20);let start={base}+32*k;
 {obs}
 let old=out[j];out[start..start+32].copy_from_slice(&bytes);
 assert_eq!(out[j],{expect});
}}
'''
s+='''
// nth initializes the arbitrary pre-state; exactly one next is the tested step.
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_frontier_iterator_step(){
 let rows=NBN_frontier(); let k:usize=kani::any();kani::assume(k<=20);
 let mut iter=rows.iter().enumerate();
 if k>0 {let _=iter.nth(k-1);}
 assert_eq!(iter.next_index(),k);
 let value=iter.next();
 if k<20 {
   let (level,row)=value.unwrap();assert_eq!(level,k);
   assert!(core::ptr::eq(row,&rows[k]));
   assert_eq!(iter.next_index(),k+1);assert_eq!(iter.len(),19-k);
 } else {assert!(value.is_none());assert_eq!(iter.next_index(),20);assert_eq!(iter.len(),0);}
}
'''
p.write_text(old+s)
(E/'NBN_ROW_CUTS.json').write_text(json.dumps(dict(replacement_for='NBH K024/K025 dynamic full-store timeouts',split=['inside32-byte window','strict prefix frame','suffix frame'],graph_change='old observed scalar rather than cloned full buffer; branch-specific observation',unwind=1881,protocol_steps=1,prestate='20-row slice iterator after k consumed elements; nth only initializes prestate',feature='iter_next_index in external scratch cfg(kani) only'),indent=2)+'\n')
