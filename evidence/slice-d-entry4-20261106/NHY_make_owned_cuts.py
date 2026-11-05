from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];p=E/'NHY_auth.rs.txt';s=p.read_text().split('// NHY owned stage cuts')[0]+'\n// NHY owned stage cuts\n';source=(R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text()
# All eight actual verifier error constructors; no native String callback assumed.
errors=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']
s+='fn NHY_any_verifier_error()->verifier::Error{let tag:u8=kani::any();kani::assume(tag<8);match tag{'+','.join(str(i)+'=>verifier::Error::'+e for i,e in enumerate(errors[:-1]))+',_=>verifier::Error::Allocation}}\n'
for bad in [False,True]:
 n='stage2_tail'+('_wrong' if bad else '')
 s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(reply:Result<(),verifier::Error>,emit_ok:bool)->bool{{
 let mut error_calls=0u8;let mut emit_calls=0u8;let mut observed=None;
 let result=(||->ProgramResult{{
  reply.map_err(|e|{{error_calls+=1;observed=Some(e);ProgramError::InvalidInstructionData}})?;
  emit_calls+=1;
  if emit_ok{{Ok(())}}else{{Err(ProgramError::InvalidInstructionData)}}
 }})();
 let expected=match reply{{Ok(())=>emit_ok,Err(_)=>false}};
 let schedule=match reply{{Ok(())=>error_calls==0&&emit_calls==1&&observed.is_none(),Err(e)=>error_calls==1&&emit_calls==0&&observed==Some(e)}};
 {'!' if bad else ''}(schedule && result.is_ok()==expected && (result.is_ok()||result==Err(ProgramError::InvalidInstructionData)))
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(2)]
fn {n}(){{let reply=if kani::any(){{Ok(())}}else{{Err(NHY_any_verifier_error())}};{n}_packet(reply,kani::any());}}
'''
# Exact original guard predicates; physical windows explicitly bounded, not a root claim.
for idx,limit in [(1,3),(2,5)]:
 m=re.search(r'fn stage'+str(idx)+r'_owned\(',source);beg=source.index('    if ',m.end());end=source.index('\n    }',beg)+6;piece=source[beg:end];condition=piece[piece.index('if ')+3:piece.index('{')].strip();condition=condition.replace('accounts.len()','account_len')
 for bad in [False,True]:
  n=f'stage{idx}_header'+('_wrong' if bad else '')
  if idx==1:expect='data.len()==2 && data[0]==3 && (data[1]==10 || data[1]==11) && account_len==3'
  else:expect='account_len==7 && data.len()>=4 && data[0]==65 && data[1]==83 && data[2]==81 && data[3]==56'
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(bytes:&[u8;{limit}],n:usize,account_len:usize)->bool{{
 kani::assume(n<={limit});let data=&bytes[..n];
 let result=if {condition} {{false}}else{{true}};
 {'!' if bad else ''}(result==({expect}))
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(7)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{{n}_packet(&kani::any(),kani::any(),kani::any());}}
'''
for idx in [1,2]:
 for bad in [False,True]:
  n=f'stage{idx}_span'+('_wrong' if bad else '')
  # Stage1's proof length is frozen; stage2 admits every usize to its checked add.
  length='verifier::PROOF_BYTES' if idx==1 else 'proof_length'
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(data_len:usize,proof_length:usize)->bool{{
 let proof_start=POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
 let outcome=(||->Result<(usize,usize),ProgramError>{{
  let proof_end=proof_start.checked_add({length}).ok_or(ProgramError::InvalidAccountData)?;
  if data_len!=proof_end{{return Err(ProgramError::InvalidAccountData);}}
  Ok((proof_start,proof_end))
 }})();
 let sum=(proof_start as u128)+({length} as u128);
 let expected=if sum>usize::MAX as u128 || data_len as u128!=sum{{Err(ProgramError::InvalidAccountData)}}else{{Ok((proof_start,sum as usize))}};
 outcome{'!=' if bad else '=='}expected
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(2)]
fn {n}(){{{n}_packet(kani::any(),kani::any());}}
'''
# One require_zero loop iteration, arbitrary pre-state; exact first-error branch.
for bad in [False,True]:
 n='require_zero_step'+('_wrong' if bad else '')
 s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(bytes:&[u8;2],n:usize)->bool{{
 kani::assume(n<=2);let remaining=&bytes[..n];
 let (code,pointer,length)=if remaining.is_empty(){{(0u8,remaining.as_ptr(),0usize)}}else if remaining[0]!=0{{(1,remaining.as_ptr(),remaining.len())}}else{{let next=&remaining[1..];(2,next.as_ptr(),next.len())}};
 let good=if n==0{{code==0&&length==0}}else if bytes[0]!=0{{code==1&&pointer==remaining.as_ptr()&&length==n}}else{{code==2&&pointer==unsafe{{remaining.as_ptr().add(1)}}&&length==n-1}};
 {'!' if bad else ''}good
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{{n}_packet(&kani::any(),kani::any());}}
'''
p.write_text(s)
(E/'NHY_OWNED_CUTS.json').write_text(json.dumps(dict(stage2_tail='Full 8-label Error carrier, exact map_err/emit source order. Callback return constrained to its sole native result IID; formatter effects OPEN. emit IID/Ok domain comes from actual emit_result; no parent closure.',headers='Actual source guard conditions; physical windows len0..3 and0..5 only. All account_len usize. Not an arbitrary-length allocation claim.',span='Actual checked_add + length predicate, all usize proof/data lengths (stage1 frozen proof constant); no borrow/slicing/proof-prefix/child argument or driver closure.',require_zero='One actual source iteration on arbitrary physical 0..2-byte window. General slice length, induction and parent association remain OPEN.',source_sha256=hashlib.sha256(source.encode()).hexdigest()),indent=1)+'\n')
print('prepared owned cuts, runner publication deferred')
