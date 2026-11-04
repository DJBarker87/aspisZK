from pathlib import Path
import sys,subprocess,difflib,json,hashlib,re
E=Path(__file__).resolve().parent;kind,mode=sys.argv[1:3];assert kind in ['predicate','metadata'] and mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
p='programs/aspis-pool/src/nullifier.rs';src=read(p)
s='use super::*;\n#[kani::proof]\n#[kani::unwind(209)]\n'
s+='''#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
'''
if kind=='predicate':
 fragment=re.search(r'\.all\((\|byte\|\s*\*byte\s*==\s*0)\)',src).group(1).replace('|byte|','|byte: &u8|')
 s+='let active:bool=kani::any();let byte:u8=kani::any();let mut calls=0u8;let predicate='+fragment+';\nlet mut actual=if active{calls+=1;predicate(&byte)}else{false};\n'
 if mode=='negative':s+='actual=!actual;\n'
 s+='assert!(actual==(active&&byte==0));assert!(calls==if active{1}else{0});\n'
 domain='one native byte predicate and local short-circuit log only; actual Iterator::all step/control association remains OPEN'
else:
 s+='''let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let program=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let flags:[bool;3]=kani::any();kani::assume(flags[0]||flags[1]||!flags[2]);
 let info=AccountInfo::new(&key,flags[1],flags[2],&mut lamports,&mut bytes,&owner,flags[0],kani::any());
 let mut actual=classify_nullifier_marker_account_v1(&program,&info);
'''
 if mode=='negative':s+='actual=Ok(NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned);\n'
 s+='assert!(matches!(actual,Err(e) if e==PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));\n'
 domain='invalid-metadata rejection branch only, fixture one-byte carrier; no zero-image/borrow/marker planning or production admission credit'
s+='}\n';patch=''
for p in ['programs/aspis-pool/src/nullifier.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);hook=f+'\n#[cfg(kani)]\n#[path="NGG_Marker.rs"]\nmod NGG_Marker;\n' if p.endswith('nullifier.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NGG_Marker.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NGG_native.patch').write_text(patch);(E/'NGG_CURRENT.json').write_text(json.dumps(dict(kind='marker-'+kind,mode=mode,source=s,domain=domain,production_credit=False),indent=1)+'\n')
