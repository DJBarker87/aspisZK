from NCB_generate import *
t='\n#[cfg(kani)] mod NCB_resize_split {\nuse super::*;\n'
for n in [0,1]:
 for field in ['length','value','frame']:
  if n==0 and field=='frame':continue
  check={'length':f'assert!(out.len()=={n+1});assert!(out.as_ptr()==ptr);assert!(out.capacity()==cap);','value':f'assert!(out[{n}]==value);','frame':'assert!(out[0]==old);'}[field]
  t+='#[kani::proof] #[kani::unwind(32)]\n'+attrs+f'fn word_{n}_{field}()'+'{\n'
  t+=f'let old:u32=kani::any();let value:u32=kani::any();let mut out=Vec::<u32>::with_capacity(2);'+('out.push(old);' if n else '')+'let ptr=out.as_ptr();let cap=out.capacity();'+f'out.resize({n+1},value);'+check+'\n}\n'
t+='}\n';emit('crates/aspis-core/src/r0/heap.rs',t,'NCB_resize_split')
