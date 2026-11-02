"""Local-module replay of the exact NCN borrowed Vec/fixed-array interface."""
from NEK_priority import *
rp='evidence/native-tx2r2-20261028/NCN_K061/receipt.json'
p='crates/aspis-r1-cost-probe/src/verifier.rs'
def overlay():
 full=read_json(E/'NEK_NCN_K061_chain.json.xz')[p];h=full[full.index('#[cfg(kani)] mod NCN_vec'):];assert 'static mut' not in h
 raw=frozen(p).decode();old='let [a,b,c,d]=self.raw[index].map(M31::reduce_u64);';new='let row=NCN_vec::row(&self.raw,index);\n        let [a,b,c,d]=row.map(M31::reduce_u64);';assert raw.count(old)==1;raw=raw.replace(old,new)
 h=h.replace('NCI_kmx','crate::NEK_kmx')
 # Required per-shape fidelity admission: deliberately weak same-shape helper.
 insert='''
#[kani::requires(raw.len()==64&&index<64)]
#[kani::ensures(|out:&[u64;4]| out[0]==raw[index][0])]
fn NEK_weak(raw:&Vec<[u64;4]>,index:usize)->[u64;4]{raw[index]}
#[kani::requires(raw.len()==64&&index<64)]
#[kani::ensures(|out:&[u64;4]| out[0]==raw[index][0])]
fn NEK_bad_modifies(raw:&mut Vec<[u64;4]>,index:usize)->[u64;4]{let out=raw[index];raw[index][1]=raw[index][1].wrapping_add(1);out}
'''
 attrs='''#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEK_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEK_kmx::KMX_copy_from_slice)]
'''
 setup='let rows:[[u64;4];64]=['+','.join(['kani::any()']*64)+'];let mut raw=Vec::from(rows);let index:usize=kani::any();kani::assume(index<64);'
 insert+='#[kani::proof_for_contract(NEK_weak)]\n'+attrs+'fn NEK_weak_contract(){'+setup+'let _=NEK_weak(&raw,index);}\n'
 insert+='#[kani::proof]\n'+attrs+'fn NEK_real(){'+setup+'let out=NEK_weak(&raw,index);assert!(out[1]==raw[index][1]);}\n'
 insert+='#[kani::proof]\n#[kani::stub_verified(NEK_weak)]\n'+attrs+'fn NEK_unimplied(){'+setup+'let out=NEK_weak(&raw,index);assert!(out[1]==raw[index][1]);}\n'
 insert+='#[kani::proof_for_contract(NEK_bad_modifies)]\n'+attrs+'fn NEK_modifies(){'+setup+'let _=NEK_bad_modifies(&mut raw,index);}\n'
 h=h[:h.rfind('}')]+insert+h[h.rfind('}'):]
 o=kmx('crates/aspis-r1-cost-probe');o[p]=raw+'\n'+h
 return o

def run(start=23):
 o=overlay()
 tests=[('row_contract',False),('inverted_contract',True),('NEK_weak_contract',False),('NEK_real',False),('NEK_unimplied',True),('NEK_modifies',True),('caller_ok',False),('caller_wrong',True)]
 for i,(name,negative) in enumerate(tests):
  a=f'NEK_K{start+i:03}'
  if (E/a/'receipt.json').exists():continue
  os.environ['NEK_HARNESS']='verifier::NCN_vec::'+name
  v=publish(a,rp,o,negative,'exact NCN fixed-array reply / borrowed Vec shape with local compiled module; per-shape controls; original caller property unchanged')
  if 'error: could not compile' in (E/a/'stdout.log').read_text():raise SystemExit('own compile error; repair before dependent submission')
  if v=='OPEN':
   (E/'NEK_VEC_OPEN.md').write_text(f'{a} / {name} OPEN; no unchanged retry. Stop this Vec construction shape; next attempt must split one window with frame transport. No caller composition credit.\n')
   break
  if name=='caller_wrong':del os.environ['NEK_HARNESS']
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 23)
