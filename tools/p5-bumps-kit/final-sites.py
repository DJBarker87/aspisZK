def extend(ns):
 fn=ns['fn'];record=ns['record'];modules=ns['modules'];harnesses=ns['harnesses'];blob=ns['blob'];masked=ns['masked']
 def add(name,code,test):
  modules.append('mod '+name+' {use super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'(){reset();\n'+test+'\n}\n}\n');harnesses.append(name+'::'+name)
 # Remaining Pool Registry-v2 call sites, exact seed calls.
 p='programs/aspis-pool/src/registry.rs';o='authenticate_verifier_selection_v2';w,_=fn(p,o)
 for field in ['registry','entry']:
  marker='stored_bump_address_matches(';starts=[m.start() for m in __import__('re').finditer(__import__('re').escape(marker),w)];i=starts[0 if field=='registry' else 1];op=w.index('(',i);depth=1;j=op+1
  while depth:depth+=(w[j]=='(')-(w[j]==')');j+=1
  s=w[i:j];record(p,o,s,'complete stored-bump primitive call expression')
  seeds='[POOL_V1_VERIFIER_REGISTRY_V2_SEED,pool.as_ref(),&[registry.bump]]' if field=='registry' else '[POOL_V1_VERIFIER_ENTRY_V2_SEED,pool.as_ref(),&selection.profile_binding,&selection.release_binding,&[entry.bump]]'
  setup='let pp=any_key();let pool=&pp;let registry_program=any_key();let rk=any_key();let ek=any_key();let ra=account(&rk);let ea=account(&ek);let registry_account=&ra;let entry_account=&ea;let registry:Registry=kani::any();let entry:Registry=kani::any();let selection:Selection=kani::any();'
  add('pool_'+field+'_v2_call','use crate::registry::stored_bump_address_matches;',setup+'let accepted='+s+';if accepted{assert_eq!(memo().answer,Some(*'+field+'_account.key));assert_eq!(memo().query,query(&'+seeds+',&registry_program));}')
 for field,expected,prog in [('registry','expected_registry_programdata','registry_program'),('entry','expected_verifier_programdata','selected_program')]:
  i=w.index('let '+expected+' = Pubkey::create_program_address');end=w.index('\n    }',w.index('if '+('!registry_address_matches' if field=='registry' else 'entry.pool'),i))+len('\n    }');s=w[i:end];record(p,o,s,'complete ProgramData derivation and metadata guard slice')
  setup='let pool=any_key();let registry_program=any_key();let selected_program=any_key();let loader=any_key();let registry:Registry=kani::any();let entry:Registry=kani::any();let selection:Selection=kani::any();let policy:Policy=kani::any();let registry_address_matches:bool=kani::any();'
  add('pool_'+field+'_programdata','fn check(pool:Pubkey,registry_program:Pubkey,selected_program:Pubkey,loader:Pubkey,registry:Registry,entry:Registry,selection:Selection,policy:Policy,registry_address_matches:bool)->ProgramResult{'+s+'\nOk(())}',setup+'if check(pool,registry_program,selected_program,loader,registry,entry,selection,policy,registry_address_matches).is_ok(){assert_eq!(memo().answer,Some(Pubkey::new_from_array('+field+'.programdata_address)));assert_eq!(memo().query,query(&['+prog+'.as_ref(),&['+field+'.programdata_bump]],&loader));}')
 # Entry status/timing changes are the only post-initializer entry writers.
 V='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
 for suffix in ['','_v2']:
  t='VerifierRegistryEntry'+('V2' if suffix else 'V1');v=blob(V);si=v.index('pub struct '+t+' {');sj=v.index('\n}',si)+2;st=v[si:sj];record(V,t,st,'exact entry type reused for update')
  for action in ['activate','retire']:
   p=ns['G'];o='process_'+action+suffix;w,_=fn(p,o);i=w.index('let next_entry =');j=w.index('\n    };',i)+len('\n    };');s=w[i:j];record(p,o,s,'complete entry update constructor slice')
   src='entry' if action=='activate' else 'retiring'
   add('preserve_entry_'+action+suffix,'#[derive(Clone,Copy,kani::Arbitrary)]\n'+st, f'let {src}:{t}=kani::any();let current_slot:u64=kani::any();'+s+f'assert_eq!(next_entry.bump,{src}.bump);assert_eq!(next_entry.pool,{src}.pool);assert_eq!(next_entry.profile_binding,{src}.profile_binding);assert_eq!(next_entry.release_binding,{src}.release_binding);'+(f'assert_eq!(next_entry.programdata_bump,{src}.programdata_bump);assert_eq!(next_entry.programdata_address,{src}.programdata_address);' if suffix else ''))
 # Unused hint sentinel guards are exact frozen control flow.
 p=ns['F']
 for name,o,anchor,test in [
  ('unused_next_hint','plan_pair_forest_spend_layout_v1','if cursor == 4','if accepted&&cursor==4{assert_eq!(hints.next_page,0);}'),
  ('unused_vault_hints','process_pair_forest_terminal_with_verifier_v1','if !withdrawal','if accepted&&!withdrawal{assert_eq!(hints.vault_authority,0);assert_eq!(hints.vault_token_account,0);}')]:
  w,_=fn(p,o);i=w.index(anchor);op=w.index('{',i);m=masked(w);depth=1;j=op+1
  while depth:depth+=(m[j]=='{')-(m[j]=='}');j+=1
  s=w[i:j];record(p,o,s,'complete unused-hint rejection guard')
  add(name,'fn check(cursor:usize,withdrawal:bool,hints:TerminalHints)->ProgramResult{'+s+'\nOk(())}','let cursor:usize=kani::any();let withdrawal:bool=kani::any();let hints:TerminalHints=kani::any();let accepted=check(cursor,withdrawal,hints).is_ok();'+test)
