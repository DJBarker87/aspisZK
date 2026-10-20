"""Source-bound arithmetic summaries used by concrete domain functions."""
from pathlib import Path
import re

def build(get,blob,fn,pins,sha):
    F='crates/aspis-core/src/field.rs';D='crates/aspis-r1-cost-probe/src/fast_domain.rs'
    s='use super::*;\n'
    s+=get(F,'reduce_u64','#[kani::ensures(|r:&u32| *r<P)]')
    s+='#[kani::proof_for_contract(reduce_u64)] fn reducer(){reduce_u64(kani::any());}\n'
    s+='impl M31 {pub const ZERO:Self=Self(0);pub const ONE:Self=Self(1);\n'
    for name in ['add','sub','neg','double','mul','reduce_u64']:
        req='' if name in ['mul','reduce_u64'] else '#[kani::requires(self.0<P'+(' && rhs.0<P' if name in ['add','sub'] else '')+')]\n'
        s+=get(F,'M31::'+name,req+'#[kani::ensures(|r:&M31| r.0<P)]')
    s+='}\n'
    for name in ['add','sub','neg','double','mul','reduce_u64']:
        deps={'add':[], 'sub':[], 'neg':[], 'double':['M31::add'], 'mul':['reduce_u64'], 'reduce_u64':['reduce_u64']}[name]
        s+=f'#[kani::proof_for_contract(M31::{name})]\n'+''.join(f'#[kani::stub_verified({d})]\n' for d in deps)
        args={'add':'kani::any(),kani::any()','sub':'kani::any(),kani::any()','neg':'kani::any()','double':'kani::any()','mul':'kani::any(),kani::any()','reduce_u64':'kani::any()'}[name]
        s+=f'fn scalar_{name}() {{M31::{name}({args});}}\n'
    s+='impl CM31 {\n'
    for name in ['new','mul']:
        req='a.0<P && b.0<P' if name=='new' else 'cm_ok(self) && cm_ok(rhs)'
        s+=get(F,'CM31::'+name,f'#[kani::requires({req})]\n#[kani::ensures(|r:&CM31| cm_ok(*r))]')
    s+='}\n'
    s+='''#[kani::proof_for_contract(CM31::new)] fn complex_new(){CM31::new(kani::any(),kani::any());}
#[kani::proof_for_contract(CM31::mul)]
#[kani::stub_verified(M31::mul)] #[kani::stub_verified(M31::reduce_u64)] #[kani::stub_verified(M31::sub)]
fn complex_mul(){CM31::mul(kani::any(),kani::any());}
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct FibreIndex(usize);
impl FibreIndex {
'''
    # The source macro expands this exact constructor; bind its template.
    domain=blob('crates/aspis-core/src/r0/domain.rs').decode()
    template='''pub fn new(index: usize) -> Result<Self, Error> {
                if index < $bound {
                    Ok(Self(index))
                } else {
                    Err(Error::IndexOutOfRange)
                }
            }'''
    assert template in domain
    expanded=template.replace('$bound','262144').replace('Error::IndexOutOfRange','Error::Checkpoint')
    s+='#[kani::ensures(|r:&Result<Self,Error>| r.as_ref().map_or(true, |u|u.0<262144))]\n'+expanded+'\n'
    s+='pub const fn get(self)->usize {self.0}\n}\n'
    pins.append(dict(path='crates/aspis-core/src/r0/domain.rs',owner='index_type!::FibreIndex::new',sha256=sha(template.encode()),body_edit='expand bound FIBRE_COUNT=262144; map sole error discriminant to local Checkpoint; source-shaped private newtype'))
    s+='#[kani::proof_for_contract(FibreIndex::new)] fn fibre_index(){FibreIndex::new(kani::any());}\n'
    s+='#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct Point<T>{x:T,y:T}\n'
    # Copy complete immutable tables from the frozen source, not literal substitutes.
    text=blob(D).decode()
    for name in ['TABLE_A','TABLE_B']:
        table=re.search(r'const '+name+r':.*?\n\];',text,re.S).group()
        s+=table+'\n';pins.append(dict(path=D,owner=name,sha256=sha(table.encode()),body_edit='none'))
    s+=get(D,'table_value','#[kani::requires(value.0<P && value.1<P)]\n#[kani::ensures(|r:&CM31| cm_ok(*r))]')
    s+='#[kani::proof_for_contract(table_value)] #[kani::stub_verified(CM31::new)] fn table_pair(){table_value(kani::any());}\n'
    s+=get(D,'fibre_point','#[kani::requires(u.0<262144)]\n#[kani::ensures(|r:&Point<M31>| r.x.0<P && r.y.0<P)]')
    s+='''#[kani::proof_for_contract(fibre_point)]
#[kani::stub_verified(table_value)] #[kani::stub_verified(CM31::mul)]
fn fibre_coordinates(){fibre_point(kani::any());}
'''
    s+=get(D,'line_node','#[kani::requires(u.0<262144)]\n#[kani::ensures(|r:&M31| r.0<P)]')
    s+='''#[kani::proof_for_contract(line_node)]
#[kani::stub_verified(fibre_point)] #[kani::stub_verified(M31::mul)]
#[kani::stub_verified(M31::double)] #[kani::stub_verified(M31::sub)]
fn line_coordinate(){line_node(kani::any());}
'''
    return s
