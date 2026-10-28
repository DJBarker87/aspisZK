from NCN_extend import E,current,attrs
import difflib,json
s=current();original='let [a,b,c,d]=self.raw[index].map(M31::reduce_u64);'
assert s.count(original)==1
replacement='''let row={#[cfg(kani)] {NCN_vec::row(&self.raw,index)} #[cfg(not(kani))] {self.raw[index]}};
        let [a,b,c,d]=row.map(M31::reduce_u64);'''
out=s.replace(original,replacement)
# The finish gate composes the verified row getter and snapshots that same
# allocated Vec, rather than proving the constructor copy again under modulo.
for name in ['finish_ok','finish_wrong']:
 start=out.index('fn '+name+'()')
 end=out.index('\n}',start)+2
 part=out[start:end]
 part=part.replace('let ptr=state.raw.as_ptr();','let ptr=state.raw.as_ptr();let source=state.raw[i][j];let frame=state.raw[k][j];')
 out=out[:start]+part+out[end:]
 out=out.replace('fn '+name+'()', '#[kani::stub_verified(NCN_vec::row)]\nfn '+name+'()')

h='''
#[cfg(kani)] mod NCN_vec {
use super::*;
#[kani::requires(raw.len()==64&&index<64)]
#[kani::ensures(|out:&[u64;4]| *out==raw[index])]
pub(super) fn row(raw:&Vec<[u64;4]>,index:usize)->[u64;4]{raw[index]}
#[kani::requires(raw.len()==64&&index<64)]
#[kani::ensures(|out:&[u64;4]| *out!=raw[index])]
fn inverted(raw:&Vec<[u64;4]>,index:usize)->[u64;4]{raw[index]}
'''
qs=[]
for name,neg in [('row',False),('inverted',True)]:
 h+=attrs.replace('#[kani::proof]',f'#[kani::proof_for_contract({name})]')+f'''fn {name}_contract(){{let rows:[[u64;4];64]=['''+','.join(['kani::any()']*64)+f'''];let raw=Vec::from(rows);let index:usize=kani::any();let _={name}(&raw,index);}}\n'''
 qs.append(dict(harness='verifier::NCN_vec::'+name+'_contract',negative=neg))
for neg in [False,True]:
 name='caller_'+('wrong' if neg else 'ok')
 h+=attrs+'#[kani::stub_verified(row)]\n#[kani::stub(aspis_core::field::M31::reduce_u64,reduce)]\n'+f'''fn {name}(){{let rows:[[u64;4];64]=['''+','.join(['kani::any()']*64)+f'''];let state=BatchedWeights{{raw:Vec::from(rows),terms:kani::any()}};let index:usize=kani::any();let j:usize=kani::any();kani::assume(index<64&&j<4);let source=state.raw[index][j];let value=state.value(index);let limbs=[value.c0.a.0,value.c0.b.0,value.c1.a.0,value.c1.b.0];assert!((limbs[j] as u64){'!=' if neg else '=='}source%2147483647);}}\n'''
 qs.append(dict(harness='verifier::NCN_vec::'+name,negative=neg))
h+='fn reduce(x:u64)->M31{let z:u32=kani::any();kani::assume(z as u64==x%2147483647);M31(z)}\n}\n'
out+=h
(E/'NCN_vec_contract.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),out.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs')))
(E/'NCN_vec_contract_queue.json').write_text(json.dumps(qs,indent=2)+'\n')
