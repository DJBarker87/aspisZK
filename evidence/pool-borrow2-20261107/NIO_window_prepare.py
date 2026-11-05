"""One-window split of actual checkpoint suffix; full-sized arbitrary carriers."""
from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs
from NIO_frozen_identity import frozen
text=frozen()['programs/aspis-pool/src/pair_forest.rs'].decode()
a=text.index('    let mut master_data = master.try_borrow_mut_data()?;',text.index('pub(crate) fn process_pair_forest_checkpoint_with_runtime_v1'))
b=text.index('    Ok(())',a)+len('    Ok(())');original=text[a:b]
body=original.replace('checkpoint_data.copy_from_slice(&planned.checkpoint_image);','checkpoint_data[jc..jc+1].copy_from_slice(&planned.checkpoint_image[jc..jc+1]);').replace('master_data.copy_from_slice(&planned.next_master_image);','master_data[jm..jm+1].copy_from_slice(&planned.next_master_image[jm..jm+1]);')
assert body.replace('checkpoint_data[jc..jc+1].copy_from_slice(&planned.checkpoint_image[jc..jc+1]);','checkpoint_data.copy_from_slice(&planned.checkpoint_image);').replace('master_data[jm..jm+1].copy_from_slice(&planned.next_master_image[jm..jm+1]);','master_data.copy_from_slice(&planned.next_master_image);')==original
(E/'NIO_CHECKPOINT_WINDOW_SOURCE.json').write_text(json.dumps(dict(original=original,window=body,source_sha256=hashlib.sha256(text.encode()).hexdigest(),substitution_exact=True),indent=2)+'\n')
mode=int(sys.argv[1]);negative=sys.argv[2]=='negative'
head="use super::*;\nfn NIO_window(master:&AccountInfo<'_>,checkpoint:&AccountInfo<'_>,planned:&PlannedPairForestCheckpointAccountsV1,jm:usize,jc:usize)->ProgramResult{\n"+body+'\n}\n'
s=''
for i,n in enumerate([384,192]):
 s+=f'let k{i}=Pubkey::new_from_array(kani::any());let mut l{i}:u64=kani::any();let mut d{i}:[u8;{n}]=kani::any();let a{i}=AccountInfo::new(&k{i},false,true,&mut l{i},&mut d{i},&k{i},false,0);\n'
s+='let jm:usize=kani::any();kani::assume(jm<384);let jc:usize=kani::any();kani::assume(jc<192);let km:usize=kani::any();kani::assume(km<384 && km!=jm);let kc:usize=kani::any();kani::assume(kc<192 && kc!=jc);\n'
s+='let oldm=a0.try_borrow_data().unwrap()[jm];let oldc=a1.try_borrow_data().unwrap()[jc];let framem=a0.try_borrow_data().unwrap()[km];let framec=a1.try_borrow_data().unwrap()[kc];\n'
s+='let plan=PlannedPairForestCheckpointAccountsV1{master:Pubkey::new_from_array(kani::any()),checkpoint:Pubkey::new_from_array(kani::any()),lane_sequences:kani::any(),next_master_image:kani::any(),checkpoint_image:kani::any()};\n'
if mode==1:s+='let ambient=a1.try_borrow_data().unwrap();\n'
if mode==2:s+='let ambient=a0.try_borrow_data().unwrap();\n'
s+='let result=NIO_window(&a0,&a1,&plan,jm,jc);\n'
s+='assert!(result=='+('Ok(())' if mode==0 else 'Err(ProgramError::AccountBorrowFailed)')+');\n'
if mode==0:s+='assert!(a0.try_borrow_data().unwrap()[jm]==plan.next_master_image[jm]);assert!(a1.try_borrow_data().unwrap()[jc]==plan.checkpoint_image[jc]);\n'
else:s+='assert!(a0.try_borrow_data().unwrap()[jm]==oldm);assert!(a1.try_borrow_data().unwrap()[jc]==oldc);drop(ambient);\n'
s+='assert!(a0.try_borrow_data().unwrap()[km]==framem);assert!(a1.try_borrow_data().unwrap()[kc]==framec);\n'
if negative:s+='let _retained=a0.try_borrow_mut_data().unwrap();\n'
s+='assert!(a0.try_borrow_mut_data().is_ok());assert!(a1.try_borrow_mut_data().is_ok());\n'
source=head+attrs()+'\n#[kani::proof]\nfn certificate(){'+s+'}\n'
stage('programs/aspis-pool/src/pair_forest.rs',source,'checkpoint actual source suffix window',sys.argv[2],f'Full arbitrary 384/192-byte payloads and planned images; two arbitrary target and distinct frame offsets; ambient shared mode {mode}.','Original caller prefix, all numeric incoming counters, native/library interpretation and full window induction remain OPEN.',dict(expected_verdict='FAIL' if negative else 'PASS',member='process_pair_forest_checkpoint_with_runtime_v1',source_window='NIO_CHECKPOINT_WINDOW_SOURCE.json'))
print('Checkpoint source window prepared')
