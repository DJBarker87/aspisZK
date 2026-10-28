from pathlib import Path
import re,json,subprocess
E=Path(__file__).resolve().parent;D=E.parent/'kani-diag-20261027'
plans=json.loads((D/'KDX_REPLAY_PLAN_INITIAL.json').read_text());out=[]
attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
'''
for x in plans:
 p=D/(x['module']+'.rs.txt');s=p.read_text().replace('KDX_','KMX_')
 s=s.replace('#[kani::proof]','#[kani::proof]\n'+attrs)
 m=x['module'].replace('KDX_','KMX_');(E/(m+'.rs.txt')).write_text(s)
 out.append({**x,'module':m,'harness':x['harness'].replace('KDX_','KMX_'),'path':x['path'].replace('KDX_','KMX_')})
(E/'KMX_REPLAY_PLAN.json').write_text(json.dumps(out,indent=2)+'\n')
# Scratch-only parent overlays; repository release files are never changed.
payload={}
for parent in {x['parent'] for x in out}:
 path='crates/aspis-r1-cost-probe/src/'+parent+'.rs'
 text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
 for x in out:
  if x['parent']==parent:text+='\n#[cfg(kani)]\n#[path="'+x['module']+'.rs"]\nmod '+x['module']+';\n'
 payload[path]=text
(E/'KMX_parent_payload.json').write_text(json.dumps(payload,indent=2)+'\n')
