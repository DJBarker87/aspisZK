# Archived initial generator; final compiled inputs include later revisions.
# Use KNH_RESULTS.json/source hashes and committed rs.txt files for replay.
from pathlib import Path
import json
E=Path(__file__).resolve().parent
shapes={
'slice':("&'a [u8]",'input','r.len()==1','r[0]'),
'result_slice':("Result<&'a [u8],u8>",'Ok(input)','matches!(r,Ok(v) if v.len()==1)','r.as_ref().unwrap()[0]'),
'vec':('Vec<u8>','{let mut v=Vec::with_capacity(1);v.push(input[0]);v}','r.len()==1','r[0]'),
'result_vec':('Result<Vec<u8>,u8>','{let mut v=Vec::with_capacity(1);v.push(input[0]);Ok(v)}','matches!(r,Ok(v) if v.len()==1)','r.as_ref().unwrap()[0]'),
'box':('Box<u8>','Box::new(input[0])','true','**r')}
stubs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
'''
plan=[]
for shape,(ty,body,length,read) in shapes.items():
 pre='#[kani::requires(input.len()==1)]\n'
 s='#![feature(allocator_api)]\nextern crate alloc;\nuse alloc::{vec::Vec,boxed::Box};\n#[cfg(kani)] mod KMX_stubs;\n'
 for kind,post,mutation in [('weak',length,''),('inverted',f'({length}) && ({read}) != input[0]',''),('frame',length,'a[0]=1;b[0]=2;')]:
  args="input:&'a [u8]" if kind!='frame' else "input:&'a [u8],a:&mut [u8;1],b:&mut [u8;1]"
  s+=pre+('#[kani::modifies(a)]\n' if kind=='frame' else '')+f'#[kani::ensures(|r: &{ty}| {post})]\nfn KNH_{kind}<\'a>({args})->{ty}{{{mutation}{body}}}\n'
 init='let input:[u8;1]=kani::any();'
 # Six separate invocations per shape. Controls pair weak real/stub with same assertion.
 for kind in ['weak','inverted','real','stub','frame','frame_real']:
  attr=f'#[kani::proof_for_contract(KNH_{kind})]\n' if kind in ['weak','inverted','frame'] else '#[kani::proof]\n'
  if kind=='stub':attr+='#[kani::stub_verified(KNH_weak)]\n'
  if kind in ['weak','inverted']:hbody=init+f'let _=KNH_{kind}(&input);'
  elif kind in ['real','stub']:hbody=init+f'let out=KNH_weak(&input);let r=&out;assert!(({length}) && ({read})==input[0]);'
  else:hbody=init+'let mut a=[0u8];let mut b=[0u8];let _=KNH_frame(&input,&mut a,&mut b);'+('assert!(a[0]==1 && b[0]==2);' if kind=='frame_real' else '')
  s+=attr+stubs+f'#[kani::unwind(8)]\nfn KNH_{shape}_{kind}(){{{hbody}}}\n'
  plan.append(dict(group='shape',shape=shape,harness=f'KNH_{shape}_{kind}',source=f'KNH_{shape}.rs.txt',expected='PASS' if kind in ['weak','real','frame_real'] else 'FAIL'))
 (E/f'KNH_{shape}.rs.txt').write_text(s)
# Exact KMX replacement source extracted from the approved patch, not independently authored.
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text();part=patch.split('diff --git a/KMX_native.rs')[0]
kmx='\n'.join(l[1:] for l in part.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n'
(E/'KNH_KMX_stubs.rs.txt').write_text(kmx)
# Loop probes are standalone diagnostics, not a whole-buffer implementation bridge.
s='#![feature(proc_macro_hygiene,stmt_expr_attributes)]\n'
for neg in [False,True]:
 name='KNH_for_'+('negative' if neg else 'positive')
 s+=f'''#[kani::proof]
fn {name}(){{let a:[u8;4]=kani::any();let mut count:usize=0;
 #[kani::loop_invariant(count == kani::index && count <= 4)]
 for _x in a.iter().enumerate(){{count+=1;}}
 assert_eq!(count,{3 if neg else 4});
}}
'''
 plan.append(dict(group='loop',harness=name,source='KNH_loops.rs.txt',expected='FAIL' if neg else 'PASS'))
s+='struct KNH_Record {bytes:[u8;4]}\n'
for neg in [False,True]:
 name='KNH_borrowed_'+('negative' if neg else 'positive')
 s+=f'''#[kani::proof]
fn {name}(){{let record=KNH_Record{{bytes:kani::any()}};let borrowed=&record;let mut i=0usize;
 #[kani::loop_invariant(i<=borrowed.bytes.len())]
 while i<borrowed.bytes.len(){{i+=1;}}
 assert_eq!(i,{3 if neg else 4});
}}
'''
 plan.append(dict(group='loop',harness=name,source='KNH_loops.rs.txt',expected='FAIL' if neg else 'PASS'))
(E/'KNH_loops.rs.txt').write_text(s)
# Preserve historical NBZ minimal symbols; only experimental module naming changes.
base=Path('evidence/kani-diag2-20261028/KNB_MINIMAL.rs.txt').read_text().replace('use super::*;','')
context='#[derive(Clone,Copy)]\nenum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }\ntype Observer=Option<fn(Phase)>;\n'
for kind,module,body in [('baseline','NBZ_native',base),('some_false','NBZ_native',base.replace('obs.is_none()','obs.is_some()')),('payload_false','NBZ_native',base.replace('assert_eq!(i,NBZ_Q)','assert!(i >= 10)')),('module_only','KNC_native',base)]:
 name=f'KNH_k2_{kind}.rs.txt';(E/name).write_text(context+f'#[cfg(kani)] mod {module} {{ use super::*;\n'+body+'\n}\n')
 plan.append(dict(group='k2',harness=f'{module}::NBZ_return_carriers',source=name,expected='diagnostic'))
# Exact 55-configuration KMX source plus a second version registering the approved mitigations.
s=Path('evidence/kani-mitig-20261028/KMX_trigger.rs.txt').read_text()
for kind in ['builtin','mitigated']:
 body=s
 if kind=='mitigated':
  # Generic registrations cover all T:Copy, as in the approved source.
  attrs=stubs.replace('<[u8]>','<[u32]>').replace('::<u8>','::<u32>')
  body=body.replace('#[kani::proof]', '#[kani::proof]\n'+attrs)
 (E/f'KNH_copy_{kind}.rs.txt').write_text('#![feature(allocator_api)]\nextern crate alloc;\n#[cfg(kani)] mod KMX_stubs;\n'+body)
 plan.append(dict(group='copy',harness='KMX_',source=f'KNH_copy_{kind}.rs.txt',expected='per-harness correct PASS wrong FAIL',exact=False))
assert len(plan)==40
(E/'KNH_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
(E/'KNH_Cargo.toml.txt').write_text('[package]\nname="knh-sandbox"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[profile.dev]\nopt-level=3\ndebug=0\noverflow-checks=true\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
