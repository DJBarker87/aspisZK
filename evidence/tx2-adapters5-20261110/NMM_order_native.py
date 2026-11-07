"""Whole frozen217 ordered-prefix check; no callee laws in Rust."""
from NMM_bl_lane import COMMON,ANN,P
from NMM_native import *
def attempt(a,mode):
 text=COMMON.replace('#[repr(C,align(4))]','#[repr(C,align(8))]')
 text=text.replace('flags:UnsafeCell<[u8;768]> }','flags:UnsafeCell<[u8;768]>, order:UnsafeCell<usize> }')
 text=text.replace('(*args).get().write(*bytes);','(*args).get().cast::<*const u8>().write(bytes.as_ptr());')
 words='['+','.join('M31(raw['+str(i)+'])' for i in range(8))+']';text=text.replace('raw.map(M31)',words)
 hook='''let command=*(p.add(776));assert!(command>0&&command<=21,"record command domain");kani::assume(command>0&&command<=21);
  let offset=if command==1 {96}else{128+32*(usize::from(command)-2)};
  let record=&*(p.sub(offset) as *const NMM_Input);
  assert!(*record.order.get()==usize::from(command)-1,"exact next source occurrence");
  *record.order.get()=usize::from(command);
  '''
 text=text.replace('let p=bytes.as_ptr();','let p=bytes.as_ptr();\n  '+hook,1)
 text+='''
fn NMM_arguments()->[u8;768]{let mut a=[0;768];a[104]=1;for level in 0..20 {a[136+32*level]=(level+2) as u8;}a}
'''+ANN+'''fn stage(){
 let input=NMM_Input{bytes:kani::any(),args:UnsafeCell::new(NMM_arguments()),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768]),order:UnsafeCell::new(0)};
 let observer:usize=kani::any();kani::assume(observer<768);let before=input.bytes[observer];
 let native=decode_lane_from_pool_release(&input.bytes);
 let count=unsafe{*input.order.get()};assert!(count<=21,"bounded stopped/returning prefix");
 let slot=if observer==96 {Some(1)}else if observer>=128&&observer<=736&&observer%32==0 {Some((observer-128)/32+2)}else{None};
 let tag=unsafe{(*input.flags.get())[observer]};
 match slot{Some(number)=>assert!((tag>0)==(count>=number),"exact recorded prefix membership"),None=>assert!(tag==0,"no non-source event")};
 if native.is_ok(){assert!(count==21,"success completes all source occurrences");}
 assert!(input.bytes[observer]==before,"complete immutable input frame");
}
'''
 if mode=='spec':text=text.replace('==usize::from(command)-1,','==usize::from(command),')
 if mode=='argument':text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let other=NMM_Input{bytes:input.bytes,args:UnsafeCell::new(NMM_arguments()),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768]),order:UnsafeCell::new(0)};let native=decode_lane_from_pool_release(&other.bytes);')
 if mode=='footprint':text=text.replace('*record.order.get()=usize::from(command);','let _=command;')
 if mode=='copy':text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let src:[u32;8]=kani::any();let mut dst=[0u32;8];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),8)};assert!(dst!=src,"copy negative");let native=decode_lane_from_pool_release(&input.bytes);')
 return submit(a,'r1_pool_adapter::NMM_order::stage',P,'NMM_order',text,mode)
if __name__=='__main__':
 import sys
 r=attempt(*sys.argv[1:]);sys.exit(r['exit_status'])
