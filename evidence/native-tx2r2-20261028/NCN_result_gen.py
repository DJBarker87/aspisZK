from NCN_extend import E,current,attrs
import difflib,json
s=current();out=s
old='    fn k(&mut self)->Result<K,Error>'
assert out.count(old)==1
out=out.replace(old,'''    #[cfg_attr(kani,kani::requires(self.bytes.len()==1768 && self.at<=1752))]
    #[cfg_attr(kani,kani::modifies(&mut self.at))]
    #[cfg_attr(kani,kani::ensures(|_: &Result<K,Error>| self.at==old(self.at)+16))]
'''+old)
h='\n#[cfg(kani)] mod NCN_result {\nuse super::*;\n'
for name,bad,modifies in [('inverted',True,True),('bad_modifies',False,False)]:
 h+=f'''#[kani::requires(r.bytes.len()==1768&&r.at<=1752)]
#[kani::modifies({'&mut r.at' if modifies else ''})]
#[kani::ensures(|_:&Result<K,Error>| r.at{'!=' if bad else '=='}old(r.at)+16)]
fn {name}(r:&mut Reader<'_>)->Result<K,Error>{{r.k()}}
'''
qs=[]
for name,neg in [('inverted',True),('bad_modifies',True),('Reader::k',False)]:
 harness=name.replace('::','_')+'_contract'
 h+=attrs.replace('#[kani::proof]',f'#[kani::proof_for_contract({name})]')+f'''fn {harness}(){{let bytes:[u8;1768]=kani::any();let start:usize=kani::any();let mut r=Reader{{bytes:&bytes,at:start}};let _={'r.k()' if name=='Reader::k' else name+'(&mut r)'};}}\n'''
 qs.append(dict(harness='verifier::NCN_result::'+harness,negative=neg))
for name,stub,neg in [('real_implied',False,False),('stub_unimplied',True,True),('stub_cursor',True,False),('stub_cursor_wrong',True,True)]:
 h+=attrs+('#[kani::stub_verified(Reader::k)]\n' if stub else '')+f'''fn {name}(){{let bytes=[0u8;1768];let start:usize=kani::any();kani::assume(start<=1752);let mut r=Reader{{bytes:&bytes,at:start}};let out=r.k();assert!({('r.at'+('!=' if neg else '==')+'start+16') if 'cursor' in name else 'out.is_ok()'});}}\n'''
 qs.append(dict(harness='verifier::NCN_result::'+name,negative=neg))
h+='}\n';out+=h
(E/'NCN_result.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),out.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs')))
for i,q in enumerate(qs,20):q.update(attempt=f'NCN_K{i:03}',patch='NCN_result.patch')
(E/'NCN_result_queue.json').write_text(json.dumps(qs,indent=2)+'\n')
