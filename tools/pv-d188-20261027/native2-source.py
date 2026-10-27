from pathlib import Path
import json,hashlib,shutil
out=Path('evidence/pv-d188-20261027/tests');d=out/'native2-files';(d/'field').mkdir(parents=True,exist_ok=True)
for p in ['field.rs','field/wide_exact.rs','field/ct.rs']:shutil.copyfile('crates/aspis-core/src/'+p,d/p)
bindings=[]
def item(path,needle):
 t=Path(path).read_text();a=t.index(needle);b=t.index('{',a);depth=1;i=b+1
 while depth:
  if t[i]=='{':depth+=1
  elif t[i]=='}':depth-=1
  i+=1
 text=t[a:i];bindings.append(dict(path=path,line=t.count('\n',0,a)+1,sha256=hashlib.sha256(text.encode()).hexdigest(),text=text));return text
core='crates/aspis-core/src/';lib='tools/pv-cblib-20261027/lib.rs'
s='mod field;use field::{QM31,CM31,M31,WideExact as E};\n'
s+=item(core+'state_only_prefix.rs','fn state_only_statement_points')+'\n'
s+='const STATE_ONLY_HIDING_CONTEXT_BYTES:usize=81;const STATE_ONLY_HIDING_CONTEXT_VERSION:u8=1;\n'
s+=item(core+'state_only_hiding.rs','pub struct StateOnlyHidingContext')+'\n'
s+='impl StateOnlyHidingContext{'+item(core+'state_only_hiding.rs','pub fn encode(self)')+'}\n'
s+=item('crates/aspis-r1-cost-probe/src/prover_powers.rs','pub fn powers')+'\n'
s+=item(lib,'pub fn array_reference')+'\n'
for n in ['sha_pad_zero','sha_pad_suffix8','sha_pad_owned_split8']:s+=item(lib,'pub fn '+n)+'\n'
s+=item(lib,'mod sha_fallback_consts')+'\n'+item(lib,'pub mod sha_fallback_reference')+'\n'
s+='''fn main(){
 let q=QM31{c0:CM31{a:M31(2),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}};
 let z=state_only_statement_points(&[q;10]);println!("statement {:?}",z.map(|a|a.map(|q|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0])));
 let c=StateOnlyHidingContext{statement_digest:[2;32],mask_nonce:[3;32],mask_layout_fingerprint:4,layout_factor_fingerprint:5};println!("context {:?}",c.encode());
 let x=E::from_limbs([2,0,0,0,0,0,0,0]).unwrap();println!("powers {:?}",powers::<3>(x));
 println!("array {:?}",array_reference::<u32,4>(&[1,2,3,4],0));
 println!("pad {:?}",sha_pad_zero([255;64],3));
 println!("suffix {:?}",sha_pad_suffix8([255;64],[7;8]));
 println!("sha {:?}",sha_fallback_reference::extracted_block([1;8],[2;16]));
}
'''
(d/'native2.rs').write_text(s)
Path('evidence/pv-d188-20261027/native2-source-binding.json').write_text(json.dumps(dict(fragments=bindings,field_files={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*.rs') if p.name!='native2.rs'},note='Unmodified function/module text; normal native primitive/library execution; source features default, no stand-in arithmetic.'),indent=2)+'\n')
