#!/usr/bin/env python3
"""Bind step cuts to exact shipped statements; never change shipped code."""
from pathlib import Path
import hashlib,json,sys,subprocess
T=Path(__file__).resolve().parent;R=T.parents[1]
V=R/'crates/aspis-r1-cost-probe/src/verifier.rs'
text=V.read_text(); pins=[]
def cut(label,statement):
 assert statement in text,label
 pins.append(dict(label=label,path=str(V.relative_to(R)),statement=statement,sha256=hashlib.sha256(statement.encode()).hexdigest()))
 return statement
out='use super::*;\n'
for j in range(4):
 body=cut('residue-add', 'row[j]=old+u64::from(limb)*u64::from(basis.0);')
 fold=cut('residue-fold','*limb=(*limb&0x7fff_ffff)+(*limb>>31);')
 out+=f'''#[kani::requires(raw<=u64::MAX-u64::from(limb)*u64::from(basis.0))]
#[kani::ensures(|r:&u64| *r==scalar_spec(raw,limb,basis.0,flush))]
fn lane{j}(raw:u64,limb:u32,basis:M31,flush:bool)->u64 {{
 let mut row=[0;4]; let j={j}; let old=raw;
 {body}
 if flush {{let limb=&mut row[j]; {fold}}}
 row[j]
}}
#[kani::proof_for_contract(lane{j})]
#[kani::unwind(6)]
fn lane{j}_contract() {{lane{j}(kani::any(),kani::any(),kani::any(),kani::any());}}
'''
rowbody=cut('row-driver','''let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];''')
push=cut('push-row','''let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush);''')
# The cut changes the mutable scalar statements into proved value-return calls.
# Four-lane fusion itself is already kernel checked in S7OwnedP6RowContract.
out+='''#[kani::requires(k_ok(power) && basis.0<P && row_safe(row,power,basis))]
#[kani::ensures(|r:&[u64;4]| row_equal(*r,row_spec(row,power,basis,flush)))]
fn row_step(row:[u64;4],power:K,basis:M31,flush:bool)->[u64;4] {
'''+rowbody+'''
 [lane0(row[0],limbs[0],basis,flush),lane1(row[1],limbs[1],basis,flush),
  lane2(row[2],limbs[2],basis,flush),lane3(row[3],limbs[3],basis,flush)]
}
#[kani::proof_for_contract(row_step)]
#[kani::stub_verified(lane0)] #[kani::stub_verified(lane1)]
#[kani::stub_verified(lane2)] #[kani::stub_verified(lane3)]
#[kani::unwind(6)]
fn row_step_contract(){row_step(kani::any(),kani::any(),kani::any(),kani::any());}
'''
# An exact row driver cut with the contract-annotated row implementation.
out+='''struct BatchedWeights { raw:Vec<[u64;4]>,terms:usize }
fn update_residue_row(row:&mut[u64;4],power:K,basis:M31,flush:bool){*row=row_step(*row,power,basis,flush);}
impl BatchedWeights {
fn push(&mut self,index:usize,power:K,basis:M31) {
'''+push+'''
}
}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)]
fn accumulator_row_step() {
 let rows:[[u64;4];64]=kani::any(); let j:usize=kani::any();let observe:usize=kani::any();
 kani::assume(j<64 && observe<64);
 let power:K=kani::any();let basis:M31=kani::any();let terms:usize=kani::any();
 kani::assume(k_ok(power) && basis.0<P && terms<22 && row_safe(rows[j],power,basis));
 let mut weights=BatchedWeights{raw:rows.to_vec(),terms};
 weights.push(j,power,basis);
 let expected=if observe==j {row_spec(rows[j],power,basis,terms&3==3)} else {rows[observe]};
 assert!(row_equal(weights.raw[observe],expected));
 assert_eq!(weights.raw.len(),64); assert_eq!(weights.terms,terms);
}
'''
for label,stmt in [('basis-block','basis[n+j]=basis[j].mul(node);'),('prefix-push','prefixes.push(product);'),('prefix-mul','product=product.mul(value);'),('inverse-write','flat_inverse[i]=suffix_inverse.mul(prefixes[i]);'),('inverse-suffix','suffix_inverse=suffix_inverse.mul(flat[i]);')]:cut(label,stmt)
files={'src/steps.rs':out}
pins=dict(frozen_revision='b2727acd3',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(V.read_bytes()).hexdigest(),cuts=pins,scope='Fixed 64-weight production row step; scalar calls are contract cuts, fusion is separately checked in Lean. No full accumulator claim.',generated={k:hashlib.sha256(v.encode()).hexdigest() for k,v in files.items()})
# Revision is attempt metadata rather than generated identity.
pins.pop('source_revision')
files['source-binding.json']=json.dumps(pins,indent=2)+'\n'
for rel,content in files.items():
 p=T/rel
 if '--check' in sys.argv:assert p.read_text()==content,rel
 else:p.write_text(content)
print('S7 continuation cuts checked')
