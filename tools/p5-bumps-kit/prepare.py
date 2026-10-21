#!/usr/bin/env python3
"""Copy exact frozen guard slices. No shipped source mutation or fake SDK hashing."""
import argparse,json,re
from pathlib import Path
from inventory import ROOT,OUT,FREEZE,blob,fn,sha,masked
KIT=Path(__file__).resolve().parent
F='programs/aspis-pool/src/pair_forest.rs';R='programs/r1-cost-probe/src/r1_pool_adapter.rs';G='programs/aspis-registry/src/processor.rs'
manifest=[]; modules=[]; harnesses=[]
def record(p,owner,s,kind):
    whole=blob(p);assert s in whole
    manifest.append(dict(path=p,owner=owner,line=whole.count('\n',0,whole.index(s))+1,sha256=sha(s),kind=kind,edit=('External UTF8 contract: ASCII asserted and original bytes preserved; original helper retained as audit target' if kind.startswith('UTF8 boundary') else 'none: exact frozen source text; surrounding types and externals replaced by explicit proof shims')))
def guard(p,owner,anchor):
    whole,_=fn(p,owner);m=masked(whole);i=whole.index(anchor);start=m.rfind('\n',0,i)+1
    if start==0: start=m.index('    if ')
    op=m.index('{',i);depth=1;j=op+1
    while depth:depth+=(m[j]=='{')-(m[j]=='}');j+=1
    return whole[start:j]
def segment(p,owner,start,end):
    whole,_=fn(p,owner);i=whole.index(start);j=whole.index(end,i);return whole[i:j].rstrip()
def add(name,code,setup,expected,call='check()',post=''):
    modules.append('mod '+name+' {\nuse super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'() { reset();\n'+setup+'\nlet accepted = '+call+'.is_ok();\n'+expected+'\nif accepted { assert!(memo().answer == Some(target)); }\n'+post+'\n}\n}\n')
    harnesses.append(name+'::'+name)
def wrap(name,p,owner,s,params,setup,target,seeds,prog='program_id'):
    record(p,owner,s,'guard slice')
    code='fn check('+params+') -> Result<(),ProgramError> {\n'+s+'\nOk(())\n}'
    args=','.join(re.findall(r'(\w+):',params))
    expected='if accepted { let target = '+target+'; assert_eq!(memo().query, query(&'+seeds+', &'+prog+')); assert_eq!(memo().answer,Some(target)); }'
    # Assertions are inside the accepted branch, no precondition of acceptance.
    modules.append('mod '+name+' {\nuse super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'() { reset();\n'+setup+'\nlet accepted = check('+args+').is_ok();\n'+expected+'\n}\n}\n');harnesses.append(name+'::'+name)
def build():
    # Full production leaf functions, context only changed.
    helper,_=fn('programs/aspis-pool/src/registry.rs','stored_bump_address_matches');record('programs/aspis-pool/src/registry.rs','stored_bump_address_matches',helper,'complete declaration')
    modules.append('mod registry { use super::*;\n'+helper+'\n}\n')
    common='let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();'
    for name,func in [('pool_master','master_address_matches'),('pool_lane','lane_address_matches')]:
        body,_=fn(F,func);record(F,func,body,'complete declaration')
        setup=common+' let master: Master=kani::any(); let lane:u8=kani::any();'
        call=func+'(&program_id,&master,&target)' if name=='pool_master' else func+'(&program_id,&pool,lane,bump,&target).unwrap_or(false)'
        seeds='[POOL_V1_PAIR_FOREST_MASTER_SEED,&master.identity.asset_mint,&[master.bump]]' if name=='pool_master' else '[POOL_V1_PAIR_FOREST_LANE_SEED,pool.as_ref(),&[lane],&[bump]]'
        modules.append('mod '+name+' { use super::*;\n'+body+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'(){reset();'+setup+' let accepted='+call+'; if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&'+seeds+ ',&program_id));}}\n}\n');harnesses.append(name+'::'+name)
    body,_=fn('programs/aspis-pool/src/history.rs','require_root_page_address_with_bump');record('programs/aspis-pool/src/history.rs','require_root_page_address_with_bump',body,'complete declaration')
    for role in ['genesis','current','rollover']:
        modules.append('mod page_'+role+' {use super::*;\n'+body+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn page_'+role+'(){reset();'+common+'let page:u64=kani::any(); let accepted=require_root_page_address_with_bump(&program_id,&pool,page,bump,&account).is_ok(); if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_ROOT_HISTORY_PAGE_SEED,pool.as_ref(),&page.to_le_bytes(),&[bump]],&program_id));}}\n}\n');harnesses.append('page_'+role+'::page_'+role)
    body=guard(F,'decode_retained_pair_forest_checkpoint_account_v1','if checkpoint.master')
    wrap('pool_checkpoint',F,'decode_retained_pair_forest_checkpoint_account_v1',body,'program_id: &Pubkey, expected_master: &Pubkey, account: &AccountInfo, checkpoint: &Checkpoint',common+'let expected_master=&pool;let program_id=&program_id;let account=&account;let checkpoint:&Checkpoint=&kani::any();','*account.key','[POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,expected_master.as_ref(),&checkpoint.checkpoint_sequence.to_le_bytes(),&[checkpoint.bump]]','*program_id')
    # Frozen R1 verifier: full if guards, not the older V7 verifier.
    for name,anchor,field,seeds in [
        ('verifier_master','if master.identity.pool','master','[PAIR_FOREST_MASTER_SEED,&master.identity.asset_mint,&[master.bump]]'),
        ('verifier_checkpoint','if checkpoint.master','checkpoint','[PAIR_FOREST_CHECKPOINT_SEED,master_account.key.as_ref(),&checkpoint.checkpoint_sequence.to_le_bytes(),&[checkpoint.bump]]'),
        ('verifier_lane','if selected_lane.master','selected_lane','[PAIR_FOREST_LANE_SEED,master_account.key.as_ref(),&[output_lane],&[selected_lane.bump]]')]:
        body=guard(R,'authenticate_asq8_accounts',anchor)
        params='pool_program: &Pubkey, master_account: &AccountInfo, checkpoint_account: &AccountInfo, lane_account: &AccountInfo, master: &Master, checkpoint: &Checkpoint, selected_lane: &Lane, output_lane: u8'
        setup='let pp=any_key();let pool_program=&pp;let mk=any_key();let ck=any_key();let lk=any_key();let ma=account(&mk);let ca=account(&ck);let la=account(&lk);let master_account=&ma;let checkpoint_account=&ca;let lane_account=&la;let master:&Master=&kani::any();let checkpoint:&Checkpoint=&kani::any();let selected_lane:&Lane=&kani::any();let output_lane:u8=kani::any();'
        target={'master':'*master_account.key','checkpoint':'*checkpoint_account.key','selected_lane':'*lane_account.key'}[field]
        wrap(name,R,'authenticate_asq8_accounts',body,params,setup,target,seeds,'*pool_program')
    # Registry v1/v2 address blocks in R1 adapter, each copied through rejection.
    whole,_=fn(R,'authenticate_invariant_release_registry')
    for ver in ['v1','v2']:
        for field in ['registry','entry']:
            stem='expected_'+field
            occurrences=[m.start() for m in re.finditer('let '+stem+' = Pubkey::create_program_address',whole)]
            i=occurrences[0 if ver=='v2' else 1];end=whole.index('\n        }' if ver=='v2' else '\n    }',whole.index('if '+field+'_account.key',i))+len('\n        }' if ver=='v2' else '\n    }')
            body=whole[i:end]
            params='registry_program: Pubkey, master_account: &AccountInfo, registry_account: &AccountInfo, entry_account: &AccountInfo, registry: &Registry, entry: &Registry'
            setup='let registry_program=any_key();let mk=any_key();let rk=any_key();let ek=any_key();let ma=account(&mk);let ra=account(&rk);let ea=account(&ek);let master_account=&ma;let registry_account=&ra;let entry_account=&ea;let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();'
            seeds='[VERIFIER_REGISTRY'+('_V2' if ver=='v2' else '')+'_SEED,master_account.key.as_ref(),&[registry.bump]]' if field=='registry' else '[VERIFIER_ENTRY'+('_V2' if ver=='v2' else '')+'_SEED,master_account.key.as_ref(),&PROFILE_BINDING,&RELEASE_BINDING,&[entry.bump]]'
            wrap('verifier_'+field+'_'+ver,R,'authenticate_invariant_release_registry',body,params,setup,'*'+field+'_account.key',seeds,'registry_program')
    # Both programdata fields: full derivation and whole subsequent metadata guard.
    for field,derived,prog in [('registry','registry_programdata','registry_program'),('entry','verifier_programdata','verifier_program')]:
        start=whole.index('let '+derived+' = Pubkey::create_program_address');end=whole.index('\n        }',whole.index('if '+field+'.pool',start))+len('\n        }');body=whole[start:end]
        params='registry_program: Pubkey, verifier_program: &Pubkey, loader: Pubkey, master_account: &AccountInfo, master: &Master, registry: &Registry, entry: &Registry, current_slot: u64'
        setup='let registry_program=any_key();let vp=any_key();let verifier_program=&vp;let loader=any_key();let mk=any_key();let ma=account(&mk);let master_account=&ma;let master:&Master=&kani::any();let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();let current_slot:u64=kani::any();'
        wrap('verifier_'+field+'_programdata',R,'authenticate_invariant_release_registry',body,params,setup,'Pubkey::new_from_array('+field+'.programdata_address)','['+prog+'.as_ref(),&['+field+'.programdata_bump]]','loader')
    # Vault authority exact if/else expression and vault account exact match + check.
    p='programs/aspis-pool/src/vault.rs';o='plan_legacy_withdrawal_transfer_from_identity_v1';w,_=fn(p,o)
    i=w.index('if crate::registry::stored_bump_address_matches');j=w.index('\n            hints.vault_authority,',i);s=w[i:j].rstrip().rstrip(',');record(p,o,s,'authority if/else expression')
    modules.append('mod vault_authority {use super::*; fn check(program_id:&Pubkey,pool:&Pubkey,hints:VaultBumpHintsV1,vault_authority:&AccountInfo)->Result<(),ProgramError>{let _authority='+s+';Ok(())}\n#[kani::proof]\n#[kani::unwind(200)]\nfn vault_authority(){reset();'+common+'let hints:VaultBumpHintsV1=kani::any();let accepted=check(&program_id,&pool,hints,&account).is_ok();if accepted{assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_VAULT_AUTHORITY_SEED,pool.as_ref(),&[hints.vault_authority]],&program_id));}}}\n');harnesses.append('vault_authority::vault_authority')
    i=w.index('let vault_address_ok =');j=w.index('\n    if vault.mint',i);body=w[i:j].rstrip()
    wrap('vault_token',p,o,body,'program_id: &Pubkey, pool: &Pubkey, bump_hints: Option<VaultBumpHintsV1>, vault_account: &AccountInfo',common+'let hints:VaultBumpHintsV1=kani::any();let program_id=&program_id;let pool=&pool;let bump_hints=Some(hints);let vault_account=&account;','*vault_account.key','[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,pool.as_ref(),&[bump_hints.unwrap().vault_token_account]]','*program_id')
    # B1 derive-and-compare slice; derivation helper stubbed, comparison exact.
    p='programs/aspis-pool/src/nullifier.rs';o='plan_pair_forest_nullifier_marker_consumption_v1'
    body=segment(p,o,'let pool =','    let preparation =')
    wrap('marker_b1',p,o,body,'program_id: &Pubkey, marker_account: &AccountInfo, marker: Marker',common+'let program_id=&program_id;let marker_account=&account;let marker:Marker=kani::any();','*marker_account.key','[&marker.pool,&marker.canonical_nullifier_encoding()]','*program_id')
    # Canonical initialization address gates, exact complete declarations.
    for prefix,p in [('pool','programs/aspis-pool/src/processor.rs'),('registry',G)]:
        body,_=fn(p,'plan_fresh_program_pda');record(p,'plan_fresh_program_pda',body,'complete declaration')
        modules.append('mod '+prefix+'_fresh {use super::*;'+body+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+prefix+'_fresh(){let program_id=any_key();let expected=any_key();let key=any_key();let account=account(&key);let size:usize=kani::any();let accepted=plan_fresh_program_pda(&account,&program_id,&expected,size).is_ok();if accepted{assert_eq!(key,expected);assert!(!account.executable&&!account.is_signer&&account.is_writable);assert!(account.owner==&program_id||(account.owner==&system_program::id()&&account.data_is_empty()));}}}\n');harnesses.append(prefix+'_fresh::'+prefix+'_fresh')
    from extend import extend
    extend(globals())
    import runpy
    runpy.run_path(str(KIT/'initializer-slices.py'))['extend'](globals())
    runpy.run_path(str(KIT/'extra-sites.py'))['extend'](globals())
    runpy.run_path(str(KIT/'final-sites.py'))['extend'](globals())
    runpy.run_path(str(KIT/'prepared-sites.py'))['extend'](globals())
    shim=(KIT/'shim.rs').read_text()
    constants=[]
    error_path='programs/aspis-pool/src/prepared_settlement_format.rs'
    error_source=blob(error_path);si=error_source.index('pub(crate) enum PreparedSettlementFormatErrorV1');sj=error_source.index('\n}',si)+2
    error_enum=error_source[si:sj];record(error_path,'PreparedSettlementFormatErrorV1',error_enum,'exact complete error enum; preserve Result layout')
    constants.append(error_enum)
    for path,names in [(R,['PROFILE_BINDING','RELEASE_BINDING','AUDIT_POLICY_BINDING']),('crates/aspis-statement/src/pool_v1/root_history.rs',['POOL_V1_ROOT_HISTORY_PAGE_SEED'])]:
        whole=blob(path)
        for name in names:
            start=whole.index('const '+name+':');end=whole.index(';\n',whole.index('=',start))+1
            value=whole[start:end];record(path,name,value,'frozen constant (first/default profile occurrence)')
            shim=re.sub(r'const '+name+r':.*?;', '', shim, count=1, flags=re.S) if name=='POOL_V1_ROOT_HISTORY_PAGE_SEED' else shim
            constants.append(value)
    shim=shim.replace('const PROFILE_BINDING:[u8;32]=[1;32];const RELEASE_BINDING:[u8;32]=[2;32];const AUDIT_POLICY_BINDING:[u8;32]=[3;32];','')
    files={'lib.rs':shim+'\n'+'\n'.join(constants)+'\n'+'\n'.join(modules),'Cargo.toml':'[package]\nname="p5-frozen-guards"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[profile.dev]\nopt-level=3\noverflow-checks=true\ndebug=false\n[profile.release]\nopt-level=3\noverflow-checks=true\n'}
    pins=dict(source_revision=FREEZE,source_files={p:sha(blob(p)) for p in sorted({r['path'] for r in manifest})},declarations=manifest,generated={p:sha(v) for p,v in files.items()},harnesses=harnesses,scope='Exact address guard source slices and fresh-account gates. SDK derivation and account observation are explicit shims; this is not an end-to-end SVM proof.')
    files['source-pins.json']=json.dumps(pins,indent=2)+'\n'
    return files
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
    for p,s in build().items():
        dest=KIT/'generated'/p
        if args.check:assert dest.read_text()==s,p
        else:dest.parent.mkdir(exist_ok=True,parents=True);dest.write_text(s)
    print(json.dumps(dict(harnesses=len(harnesses),source_slices=len(manifest))))
