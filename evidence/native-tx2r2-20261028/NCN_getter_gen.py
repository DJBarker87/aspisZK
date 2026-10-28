from NCN_extend import E,current,attrs
import difflib,json
s=current();out=s
h='\n#[cfg(kani)] mod NCN_getters {\nuse super::*;\n'
queue=[]
for name,ty in [('residue_limb_at','u64'),('power_limb_at','u32')]:
 var='row' if ty=='u64' else 'limbs'
 decl=f'fn {name}({var}:&[{ty};4],index:usize)->{ty}'
 assert out.count(decl)==1
 annotations=f'''#[cfg_attr(kani,kani::requires(index<4))]
#[cfg_attr(kani,kani::ensures(|out:&{ty}| *out=={var}[index]))]
'''
 out=out.replace(decl,annotations+decl)
 h+=f'''#[kani::requires(index<4)]
#[kani::ensures(|out:&{ty}| *out!={var}[index])]
fn {name}_inverted({var}:&[{ty};4],index:usize)->{ty}{{{name}({var},index)}}
'''
 for neg in [False,True]:
  func=name+('_inverted' if neg else '')
  harness=name+('_control' if neg else '_contract')
  h+=attrs.replace('#[kani::proof]',f'#[kani::proof_for_contract({func})]')+f'''fn {harness}(){{let xs:[{ty};4]=kani::any();let index:usize=kani::any();let _={func}(&xs,index);}}\n'''
  queue.append(dict(harness='verifier::NCN_getters::'+harness,negative=neg))
h+='}\n'
# Add the source-exact one-step harness, now invoking verified getter contracts.
body=(E/'NCN_update.patch').read_text();lines=body.splitlines();addition='\n'.join(x[1:] for x in lines if x.startswith('+') and not x.startswith('+++'))+'\n'
addition=addition.replace('mod NCN_update','mod NCN_update').replace('#[kani::proof]','#[kani::stub_verified(residue_limb_at)]\n#[kani::stub_verified(power_limb_at)]\n#[kani::proof]')
out+=h+addition
(E/'NCN_getters.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),out.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs')))
for neg in [False,True]:queue.append(dict(harness='verifier::NCN_update::step_'+('wrong' if neg else 'ok'),negative=neg))
for i,q in enumerate(queue,9):q.update(attempt=f'NCN_K{i:03}',patch='NCN_getters.patch')
(E/'NCN_getter_queue.json').write_text(json.dumps(queue,indent=2)+'\n')
