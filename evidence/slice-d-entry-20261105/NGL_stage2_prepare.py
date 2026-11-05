from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs']
attrs='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
items=[]
# Wrapper rejection gates each isolate a distinct first guard, with arbitrary metadata unused.
for f in ['stage1','stage2']:
 for n in ([0,1,2,4] if f=='stage1' else [0,1,6,8]):
  body='let key=Pubkey::new_from_array(kani::any());let data='+('&[3u8,10][..]' if f=='stage1' else '&b"ASQ8"[..]')+';let r='+f+'(&key,&[],data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));'
  if n!=0:
   # Native AccountInfo prestate has independent key/owner/privileges/lamports/data.
   body='let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, '+str(n)+', _>(|_|a.clone());let data='+('&[3u8,10][..]' if f=='stage1' else '&b"ASQ8"[..]')+';let r='+f+'(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));'
  name=f+'_count'+str(n)
  for bad in [False,True]:
   label=name+('_wrong' if bad else '');b=body.replace(' != cfg!(NGL_invert)',' == cfg!(NGL_invert)') if bad else body
   s+='\n'+attrs+'fn '+label+'(){'+b+'}\n';items.append(label)
# Actual snapshot on borrow-failure and rejected-size paths, with account metadata arbitrary.
for fail in [False,True]:
 name='snapshot_borrow_error' if fail else 'snapshot_rejected_length'
 body='let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;5]=kani::any();let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let rent:u64=kani::any();let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes,&owner,executable,rent);'
 if fail:body+='let held=a.try_borrow_mut_data().unwrap();'
 body+='let result=core::mem::ManuallyDrop::new(snapshot(&a,1768,58295));let metadata=result.key==key&&result.owner==owner&&result.is_signer==signer&&result.is_writable==writable&&result.executable==executable;'
 body+=('let exact=metadata&&matches!(result.length,Err(ProgramError::AccountBorrowFailed))&&matches!(result.bytes,Err(ProgramError::AccountBorrowFailed));' if fail else 'let exact=metadata&&matches!(result.length,Ok(5))&&matches!(result.bytes,Err(ProgramError::InvalidAccountData));')
 if fail:body+='drop(held);'
 body+='assert!(exact != cfg!(NGL_invert));'
 for bad in [False,True]:
  label=name+('_wrong' if bad else '');b=body.replace(' != cfg!(NGL_invert)',' == cfg!(NGL_invert)') if bad else body
  s+='\n'+attrs+'fn '+label+'(){'+b+'}\n';items.append(label)
update({P+'NGL_owned.rs':s},'wrapper_snapshot_fragments')
(E/'NGL_STAGE2_TARGETS.json').write_text(json.dumps(items,indent=1)+'\n')
