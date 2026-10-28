from NCD_generate import *
p='crates/aspis-r1-cost-probe/src/transcript.rs';before=current(p);start=before.index('#[cfg(kani)] mod NCD_query_pair');s=before[start:]
s=s.replace('static mut CALLS:usize=0;static mut J:usize=0;','static mut CALLS:usize=0;static mut J:usize=0;static mut CHECK:usize=0;',1)
a='''  assert!(parts.len()==2&&parts[0].len()==32&&parts[0][J]==INITIAL[J]);
  assert!(parts[1].len()==1&&parts[1][0]==if c==0{1}else{2});'''
assert a in s;s=s.replace(a,'if c==CHECK{\n'+a+'\n}',1)
pos=s.index('fn requests(){');end=s.index('\n}\n',pos)+3;fn=s[pos:end]
add=''
for i,name in enumerate(['request_block','request_advance']):
 add+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+fn.replace('fn requests()',f'fn {name}()').replace('unsafe{CALLS=0;J=j;',f'unsafe{{CHECK={i};CALLS=0;J=j;')
pos=s.rfind('\n}');s=s[:pos]+'\n'+add+s[pos:];after=before[:start]+s
(E/'NCD_pair_split.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
