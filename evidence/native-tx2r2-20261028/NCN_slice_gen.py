from NCN_extend import E,extend,attrs
import json
h='''
#[cfg(kani)] mod NCN_slices {
use super::*;
#[kani::requires(bytes.len()==1768&&start<=1752)]
#[kani::ensures(|out: &&[u8]| out.len()==16)]
fn weak(bytes:&[u8],start:usize)->&[u8]{&bytes[start..start+16]}
#[kani::requires(bytes.len()==1768&&start<=1752)]
#[kani::ensures(|out: &&[u8]| out.len()!=16)]
fn inverted(bytes:&[u8],start:usize)->&[u8]{&bytes[start..start+16]}
#[kani::requires(bytes.len()==1768&&start<=1752&&*counter==0)]
#[kani::modifies()]
#[kani::ensures(|_: &&[u8]| true)]
fn bad_modifies<'a>(bytes:&'a[u8],start:usize,counter:&mut u8)->&'a[u8]{*counter=1;&bytes[start..start+16]}
'''
q=[]
for name,neg in [('inverted',True),('bad_modifies',True),('weak',False)]:
 harness=name+'_contract';call=name+'(&bytes,start'+(',&mut counter)' if name=='bad_modifies' else ')')
 h+=attrs.replace('#[kani::proof]',f'#[kani::proof_for_contract({name})]')+f'''fn {harness}(){{let bytes:[u8;1768]=kani::any();let start:usize=kani::any();let mut counter=0;let _={call};}}\n'''
 q.append(dict(harness='verifier::NCN_slices::'+harness,negative=neg))
for name,stub,neg in [('real_implied',False,False),('stub_unimplied',True,True),('stub_length',True,False),('stub_length_wrong',True,True)]:
 h+=attrs+('#[kani::stub_verified(weak)]\n' if stub else '')+f'''fn {name}(){{let bytes:[u8;1768]=kani::any();let start:usize=kani::any();kani::assume(start<=1752);let out=weak(&bytes,start);assert!({('out.len()'+('!=' if neg else '==')+'16') if 'length' in name else 'out[0]==bytes[start]'});}}\n'''
 q.append(dict(harness='verifier::NCN_slices::'+name,negative=neg))
h+='}\n';extend('NCN_slices.patch',h)
for i,x in enumerate(q,48):x.update(attempt=f'NCN_K{i:03}',patch='NCN_slices.patch')
(E/'NCN_slice_queue.json').write_text(json.dumps(q,indent=2)+'\n')
