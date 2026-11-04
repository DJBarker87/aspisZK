from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','index','argument','error','page']
accepted=len(sys.argv)>2 and sys.argv[2]=='accepted'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
p='programs/aspis-pool/src/pair_forest.rs';src=read(p);a=src.index('    let marker_index = cursor;',src.index('fn plan_pair_forest_spend_layout_v1'));b=src.index('\n}',a);body=src[a:b]
body=body.replace('require_exact_account_count(accounts, expected)?','count(accounts, expected)?').replace('require_unique_accounts(accounts)?','unique(accounts)?')
if mode=='argument':body=body.replace('count(accounts, expected)?','count(accounts, expected+1)?')
if mode=='error':body=body.replace('unique(accounts)?','unique(accounts).map_err(|_|ProgramError::InvalidSeeds)?')
s='use super::*;\n'
s+='''fn tail<'a,C,U>(accounts:&[AccountInfo<'a>],cursor:usize,withdrawal:bool,page:PairForestSpendPageV1,count:C,unique:U)->Result<PairForestSpendLayoutV1,ProgramError>
where C:FnOnce(&[AccountInfo<'a>],usize)->ProgramResult,U:FnOnce(&[AccountInfo<'a>])->ProgramResult{
'''+body+'\n}\n'
s+='''#[kani::proof]
#[kani::unwind(1025)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let cursor=if kani::any(){4usize}else{5usize};let withdrawal:bool=kani::any();
 let expected=cursor+8+if withdrawal{5}else{0};let actual_len:usize=kani::any();kani::assume(actual_len<=18);
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut data:[u8;1]=kani::any();let flags:[bool;3]=kani::any();
 let info=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut data,&owner,flags[2],kani::any());
 let infos:[AccountInfo<'_>;18]=core::array::from_fn(|_|info.clone());let accounts=&infos[..actual_len];
 let header=RootPageHeaderV1{pool:Pubkey::new_from_array(kani::any()),page_number:kani::any(),first_sequence:kani::any(),filled:kani::any()};
 let page=match kani::any::<u8>()%3{0=>PairForestSpendPageV1::Genesis,1=>PairForestSpendPageV1::SamePage(header),_=>PairForestSpendPageV1::Rollover{next_index:kani::any(),page_number:kani::any()}};
 let child:ProgramResult=if kani::any(){Ok(())}else{Err(ProgramError::from(kani::any::<u64>()))};
 let mut calls=0u8;
 let mut actual=tail(accounts,cursor,withdrawal,page,|args,n|{assert!(core::ptr::eq(args,accounts)&&n==expected);require_exact_account_count(args,n)},|args|{calls+=1;assert!(core::ptr::eq(args,accounts));child.clone()});
 CORRUPT
 if actual_len!=expected{assert!(calls==0);assert!(matches!(actual,Err(e) if e==if actual_len<expected{ProgramError::NotEnoughAccountKeys}else{ProgramError::InvalidArgument}));}
 else{assert!(calls==1);match child{Err(error)=>assert!(matches!(actual,Err(e) if e==error)),Ok(())=>{let l=actual.unwrap();
 assert!(l.marker_index==cursor&&l.payer_index==cursor+1&&l.system_program_index==cursor+2&&l.registry_start==cursor+3&&l.verifier_index==cursor+5&&l.proof_index==cursor+6&&l.token_start==cursor+7&&l.verifier_checkpoint_index==Some(expected-1));
 assert!(match(l.page,page){(PairForestSpendPageV1::Genesis,PairForestSpendPageV1::Genesis)=>true,(PairForestSpendPageV1::SamePage(a),PairForestSpendPageV1::SamePage(b))=>a==b,(PairForestSpendPageV1::Rollover{next_index:a,page_number:x},PairForestSpendPageV1::Rollover{next_index:b,page_number:y})=>a==b&&x==y,_=>false});
 }}}
}
'''
if accepted:
 s=s.replace('let child:ProgramResult=if kani::any(){Ok(())}else{Err(ProgramError::from(kani::any::<u64>()))};','let child:ProgramResult=Ok(());')
 s=s.replace('kani::assume(actual_len<=18);','kani::assume(actual_len==expected);')
s=s.replace('CORRUPT','if let Ok(ref mut l)=actual{l.registry_start^=1;}' if mode=='index' else 'if let Ok(ref mut l)=actual{l.page=match page{PairForestSpendPageV1::Genesis=>PairForestSpendPageV1::SamePage(header),_=>PairForestSpendPageV1::Genesis};}' if mode=='page' else '')
patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);hook=f+'\n#[cfg(kani)]\n#[path="NGG_Layout.rs"]\nmod NGG_Layout;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NGG_Layout.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NGG_native.patch').write_text(patch);(E/'NGG_CURRENT.json').write_text(json.dumps(dict(kind='layout-tail',mode=mode,accepted_only=accepted,source=s,frozen_tail_sha256=hashlib.sha256(src[a:b].encode()).hexdigest(),domain='cursor4or5; arbitrary page/header; arbitrary withdrawal; count<=18; actual count helper, full arbitrary uniqueness Result; fixture data carriers not production admission',modifies=[]),indent=1)+'\n')
