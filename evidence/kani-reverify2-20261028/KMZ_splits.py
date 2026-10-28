"""Focused heap and iterator inputs; exact KMX functions, no new copy stub."""
from KMZ_driver import *
BASE='''#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn any64()->([K;64],[[u32;4];64]){let raw:[[u32;4];64]=kani::any();(raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}),raw)}
fn words(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
'''
ATTR='''#[kani::proof] #[kani::unwind(1769)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
'''
def heap(length,cap,n,size=32,tail=False):
 return f'''let initial:[u8;1736]=kani::any();let source:[u8;{size}]=kani::any();{length}
 let cap_in={cap};let mut out=alloc::vec::Vec::with_capacity(cap_in);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..len]);
 assert_eq!(out.len(),len);assert_eq!(out.capacity(),cap_in);
 if len>0{{let p:usize=kani::any();kani::assume(p<len);assert_eq!(out[p],initial[p]);}}
 KMX_stubs::KMX_extend_from_slice(&mut out,&source);
 assert_eq!(out.len(),len+{size});
 assert_eq!(out.capacity(),if cap_in<len+{size}{{core::cmp::max(8,core::cmp::max(2*cap_in,len+{size}))}}else{{cap_in}});
 let j:usize=kani::any();kani::assume(j<out.len());
 assert_eq!(out[j],(if j<len{{initial[j]}}else{{source[j-len]}}) ^ NEG);
'''
SPLITS=[
('typed_inside','let (src,raw)=any64();let mut dst=[K::ZERO;64];KMX_stubs::KMX_copy_from_slice(&mut dst,&src);let j:usize=kani::any();kani::assume(j<64);let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(dst[j])[l],raw[j][l] ^ NEG32);',65),
('typed_exterior','let (src,_)=any64();let (edge,_)=any64();let mut dst=[K::ZERO;66];dst[0]=edge[0];dst[65]=edge[1];let j=if kani::any(){0}else{65};let old=dst[j];KMX_stubs::KMX_copy_from_slice(&mut dst[1..65],&src);let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(dst[j])[l],words(old)[l] ^ NEG32);',67),
('iterator_empty','let (src,_)=any64();let mut it=src[64..].iter();assert_eq!(it.next().is_none(),BOOL);assert_eq!(it.as_slice().len(),0);',65),
('iterator_last','let (src,raw)=any64();let mut it=src[63..].iter();let x=*it.next().unwrap();let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(x)[l],raw[63][l] ^ NEG32);assert_eq!(it.len(),0);',65),
('iterator_interior','let (src,raw)=any64();let i:usize=kani::any();kani::assume(i<63);let mut it=src[i..].iter();let x=*it.next().unwrap();let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(x)[l],raw[i][l] ^ NEG32);assert_eq!(it.len(),63-i);',65),
('iterator_suffix','let (src,raw)=any64();let i:usize=kani::any();kani::assume(i<63);let mut it=src[i..].iter();it.next();let j:usize=kani::any();kani::assume(j<63-i);let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(it.as_slice()[j])[l],raw[i+1+j][l] ^ NEG32);assert_eq!(it.len(),63-i);',65),
('clone16','let initial:[u8;16]=kani::any();let mut out=KMX_stubs::KMX_to_vec(&initial);let j:usize=kani::any();kani::assume(j<16);assert_eq!(out[j],initial[j] ^ NEG);assert_eq!(out.len(),16);',258),
]
for length,cap in [(16,16),(48,48),(80,96),(0,0),(32,32)]:SPLITS.append((f'heap_{length}_{cap}',heap(f'let len={length};',str(cap),32),258))
SPLITS += [
('query_heap',heap('let i:usize=kani::any();kani::assume(i<22);let len=64+4*i;','if i==0{64}else if i<=16{128}else{256}',4,4),258),
('owned1736','let initial:[u8;1736]=kani::any();let out=KMX_stubs::KMX_to_vec(&initial);let j:usize=kani::any();kani::assume(j<1736);assert_eq!(out[j],initial[j] ^ NEG);assert_eq!(out.len(),1736);',1769),
('retained1736',heap('let len=1736;','1736',32),1769),
('append16_any',heap('let len:usize=kani::any();kani::assume(len<=1720);','len',16,16),1769),
('append32_any',heap('let len:usize=kani::any();kani::assume(len<=1704);','len',32),1769),
('append4_any',heap('let len:usize=kani::any();kani::assume(len<=1732);','len',4,4),1769),
('selected_heap',heap('let i:usize=kani::any();kani::assume(i<64);let len=712+16*i;','len',16,16),1769),
]
# Bind the selected shared-reference serialization to this same live heap state.
SPLITS[-1]=('selected_heap',heap('let i:usize=kani::any();kani::assume(i<64);let len=712+16*i;','len',16,16).replace('let source:[u8;16]=kani::any();','let raw:[u32;4]=kani::any();let selected=K{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};let shared=&selected;let mut source=[0u8;16];shared.write_le_bytes(&mut source);').replace('source[j-len]','raw[(j-len)/4].to_le_bytes()[(j-len)%4]'),1769)

# The combined query gate timed out. Replace it by four disjoint capacity cases.
# Unrun broad generic/selected drafts are retained above for the exact remaining obligations.
SPLITS=SPLITS[:14]+[
 ('query_first',heap('let i=0usize;let len=64+4*i;','64',4,4),258),
 ('query_middle',heap('let i:usize=kani::any();kani::assume(1<=i && i<16);let len=64+4*i;','128',4,4),258),
 ('query_growth',heap('let i=16usize;let len=64+4*i;','128',4,4),258),
 ('query_last',heap('let i:usize=kani::any();kani::assume(17<=i && i<22);let len=64+4*i;','256',4,4),258),
 SPLITS[14]]

# The original checksum cut owns Vec::from(array), not the slice-to-Vec
# construction in the first draft. Keep the submitted draft as K058 and test
# the exact constructor with a new matching positive/control pair.
OWNED_ACTUAL=('owned1736_actual','let initial:[u8;1736]=kani::any();let out:alloc::vec::Vec<u8>=alloc::vec::Vec::from(initial);assert_eq!(out.len(),1736);assert_eq!(out.capacity(),1736);let j:usize=kani::any();kani::assume(j<1736);assert_eq!(out[j],initial[j] ^ NEG);',1769)
RETAINED_ACTUAL=('retained1736_actual','let initial:[u8;1736]=kani::any();let source:[u8;32]=kani::any();let mut out:alloc::vec::Vec<u8>=alloc::vec::Vec::from(initial);let p:usize=kani::any();kani::assume(p<1736);assert_eq!(out[p],initial[p]);KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.len(),1768);assert_eq!(out.capacity(),3472);let j:usize=kani::any();kani::assume(j<1768);assert_eq!(out[j],(if j<1736{initial[j]}else{source[j-1736]}) ^ NEG);',1769)
PLANS=[(split,neg) for split in SPLITS[:13] for neg in [False,True]]
PLANS += [(SPLITS[13],False),(OWNED_ACTUAL,False),(OWNED_ACTUAL,True)]
PLANS += [(split,neg) for split in SPLITS[14:18] for neg in [False,True]]
PLANS += [(RETAINED_ACTUAL,False),(RETAINED_ACTUAL,True)]
assert len(PLANS)==39

def execute(start=32):
 for number,((name,body,unwind),negative) in enumerate(PLANS,start):
   a=f'KMZ_K{number:03}'
   if number>70:return
   if (E/a/'receipt.json').exists():continue
   src=BASE+ATTR.replace('1769',str(unwind))+f'fn KMZ_{name}_gate(){{\n'+body.replace('NEG32','1u32' if negative else '0u32').replace('NEG','1u8' if negative else '0u8').replace('BOOL','false' if negative else 'true')+'}\n'
   cfg=json.loads((OLD/'KMY_K075.json').read_text());cfg.pop('deferred',None);cfg.pop('defer_reason',None)
   cfg['sources']=['KMZ_windows.rs','KMX_stubs.rs','KMY_src/Cargo.lock','KMZ_gate.py','KMY_field.rs','KMY_wide_exact.rs'];cfg['command']=['python3','KMZ_gate.py',a,'KMZ_'+name+'_gate'];cfg['negative_control']=negative;cfg['split']=name;cfg['expected_time']='optimized codegen then '+name+' selected-window CBMC; no debug arithmetic';cfg['parent_gate']=f'KMZ_K{number-1:03}' if negative else None
   result=run(a,cfg,src)
   if result=='ERROR':raise SystemExit('Inspect '+a)
if __name__=='__main__':execute()
