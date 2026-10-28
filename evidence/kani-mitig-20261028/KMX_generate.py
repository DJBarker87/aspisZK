from pathlib import Path
import json
E=Path(__file__).resolve().parent
# Sweep byte lengths within separately labelled harnesses: each controls one concrete shape.
configs=[]
for ty,w in [('u8',1),('u32',4),('u64',8),('[u8;32]',32),('KMX_Pair',8)]:
 for n in [1,2,3,4,8,16]:configs.append(dict(ty=ty,width=w,n=n,op='slice',offset=0,extra=0,dest='array'))
for size in [64,128,1024,1736,1768]:
 for ty,w in [('u8',1),('u32',4)]:configs.append(dict(ty=ty,width=w,n=size//w,op='slice',offset=0,extra=0,dest='array'))
for op in ['ptr','clone','extend','to_vec','realloc']:
 configs.append(dict(ty='u32',width=4,n=16,op=op,offset=0,extra=0,dest='vec' if op in ['extend','to_vec','realloc'] else 'array'))
for offset,extra in [(0,1),(1,1),(3,5)]:
 configs.append(dict(ty='u32',width=4,n=16,op='slice',offset=offset,extra=extra,dest='array'))
configs.append(dict(ty='u32',width=4,n=16,op='slice',offset=0,extra=0,dest='vec'))
s='''#[derive(Clone,Copy,PartialEq,Eq,Debug)]\nstruct KMX_Pair {a:u32,b:u32}\n'''
for i,c in enumerate(configs):
 c['id']=f'c{i:03}';ty=c['ty'];n=c['n'];off=c['offset'];cap=n+off+c['extra']
 zero={'u8':'0u8','u32':'0u32','u64':'0u64','[u8;32]':'[0u8;32]','KMX_Pair':'KMX_Pair{a:0,b:0}'}[ty]
 one={'u8':'1u8','u32':'512u32','u64':'512u64','[u8;32]':'[1u8;32]','KMX_Pair':'KMX_Pair{a:512,b:1}'}[ty]
 body=f'let mut input=[{zero};{n}];input[{n-1}]={one};let n:usize=kani::any();kani::assume(n=={n});'
 if c['op']=='to_vec':body+='let level=input[..n].to_vec();'
 elif c['op'] in ['extend','realloc']:
  body+=f'let mut level=Vec::<{ty}>::with_capacity('+('1' if c['op']=='realloc' else str(n))+');'
  if c['op']=='realloc':body+=f'level.push({zero});level.extend_from_slice(&input[..n]);'
  else:body+='level.extend_from_slice(&input[..n]);'
 else:
  body+=f'let mut level='+ (f'vec![{zero};{cap}]' if c['dest']=='vec' else f'[{zero};{cap}]')+';'
  if c['op']=='ptr':body+=f'unsafe{{core::ptr::copy_nonoverlapping(input.as_ptr(),level.as_mut_ptr().add({off}),n);}}'
  else:body+=f'level[{off}..{off}+n].'+('clone_from_slice' if c['op']=='clone' else 'copy_from_slice')+'(&input[..n]);'
 idx=off+n-1+(1 if c['op']=='realloc' else 0)
 for kind,expected in [('correct',one),('wrong',zero)]:
  s+=f'#[kani::proof] #[kani::unwind({max(n+3,8)})]\nfn KMX_{c["id"]}_{kind}(){{{body}assert_eq!(level[{idx}],{expected},"KMX_{c["id"]}_{kind}");}}\n'
(E/'KMX_trigger.rs.txt').write_text(s);(E/'KMX_TRIGGER_CONFIGS.json').write_text(json.dumps(configs,indent=2)+'\n')
