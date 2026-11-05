"""Frozen one-call Box wrapper, full child error carrier and local argument/place logs."""
from pathlib import Path
import sys,subprocess,re,difflib,json
E=Path(__file__).resolve().parent;family,mode=sys.argv[1:3];width=int(sys.argv[3]) if len(sys.argv)>3 else 4;assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';R=E.parents[1]
read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
src=read('programs/aspis-pool/src/pair_forest.rs')
start=src.index('fn decode_terminal_request_box_v1(');start=src.index('{',start);end=src.index('\n}',start)+2;body=src[start:end]
body=body.replace('decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)','decode(instruction_data)')
s='use super::*;\nuse aspis_statement::pool_v1::*;\n'
s+='fn digest()->aspis_statement::Digest{core::array::from_fn(|_|aspis_core::field::M31(kani::any()))}\n'
payment=read('crates/aspis-statement/src/pool_v1/payment_relation.rs')
for name in ['PoolV1PrivateTransferPublicV1','PoolV1WithdrawalPublicV1']:
 fields=re.findall(r'pub (\w+):\s*([^\n]+),',payment.split('pub struct '+name+' {',1)[1].split('\n}',1)[0])
 s+='fn any_'+name+'()->'+name+'{'+name+'{'+','.join(k+':'+('digest()' if t=='Digest' else 'aspis_core::field::M31(kani::any())' if t=='M31' else 'kani::any()') for k,t in fields)+'}}\n'
# Enumerate the complete nested finite error carrier, never u64 -> ProgramError.
index={}
for p in (R/'crates/aspis-statement/src').rglob('*.rs'):
 text=p.read_text()
 for m in re.finditer(r'pub enum (\w+)\s*\{',text):
  a=m.end();level=1;j=a
  while level:
   if text[j]=='{':level+=1
   elif text[j]=='}':level-=1
   j+=1
  index[m[1]]=re.sub(r'//[^\n]*','',text[a:j-1])
made=set()
def factory(name):
 global s
 if name in made:return 'any_'+name+'()'
 if name in ['u8','u16','u32','u64','usize','bool']:return 'kani::any()'
 assert name in index,('missing enum',name)
 made.add(name);body=index[name];parts=[];cur='';depth=0
 for c in body:
  if c=='(' :depth+=1
  if c==')' :depth-=1
  if c==',' and depth==0:
   if cur.strip():parts.append(cur.strip())
   cur=''
  else:cur+=c
 if cur.strip():parts.append(cur.strip())
 variants=[]
 for text in parts:
  m=re.fullmatch(r'(\w+)(?:\(([^()]*)\))?',text.strip());assert m,(name,text)
  n,types=m.groups();args=[]
  if types:
   for t in types.split(','):args.append(factory(t.strip()))
  variants.append(name+'::'+n+('('+','.join(args)+')' if types else ''))
 s+='fn any_'+name+'()->'+name+'{let tag:u8=kani::any();kani::assume(tag<'+str(len(variants))+');match tag{'+','.join(str(i)+'=>'+v for i,v in enumerate(variants))+',_=>unreachable!()}}\n'
 return 'any_'+name+'()'
err=factory('PoolV1PairForestTerminalFormatErrorV1')
# The place observation is explicit instrumentation in the one source expression.
if family=='place':
 body=body.replace('Ok(Box::new(', 'let boxed=Box::new(').replace('    ))\n}', '    );\n *created=Some(boxed.as_ref() as *const _);\n Ok(boxed)\n}')
 extra=',created:&mut Option<*const PoolV1PairForestTerminalRequestV1>'
else:extra=''
s+='fn wrapped<F>(instruction_data:&[u8],decode:F'+extra+')->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> where F:FnOnce(&[u8])->Result<PoolV1PairForestTerminalRequestV1,PoolV1PairForestTerminalFormatErrorV1>'+body+'\n'
s+='''#[kani::proof]
#[kani::unwind(325)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let raw:[u8;4]=kani::any();let len:usize=kani::any();kani::assume(len<=4);
 let public=if kani::any(){PoolV1PairForestTerminalPaymentV1::PrivateTransfer(any_PoolV1PrivateTransferPublicV1())}else{PoolV1PairForestTerminalPaymentV1::Withdrawal(any_PoolV1WithdrawalPublicV1())};
 let request=PoolV1PairForestTerminalRequestV1{verifier_profile:kani::any(),verifier_release:kani::any(),pool_program:kani::any(),public};
'''
s=s.replace('let raw:[u8;4]=kani::any();','let raw:[u8;'+str(width)+']=kani::any();').replace('kani::assume(len<=4);','kani::assume(len<='+str(width)+');')
s+='let error='+err+';let success='+('false' if family=='error' else 'true')+';\n'
s+='let mut calls=0usize;let mut observed=None;let mut created:Option<*const PoolV1PairForestTerminalRequestV1>=None;\n'
s+='let mut result=wrapped(&raw[..len],|arg|{calls+=1;observed=Some((arg.as_ptr(),arg.len()));if success{Ok(request)}else{Err(error)}}'+(',&mut created' if family=='place' else '')+');\n'
if mode=='negative' and family=='arguments':s+='if let Some((p,n))=observed{observed=Some((p,n^1));}\n'
if mode=='negative' and family=='error':s+='result=Err(ProgramError::InvalidArgument);\n'
if mode=='negative' and family=='place':s+='let mut retained=None;if let Ok(r)=result{let fresh=Box::new(*r);retained=Some(r);result=Ok(fresh);}\n'
s+='assert!(calls==1);assert!(observed==Some((raw.as_ptr(),len)));\n'
if family=='error':s+='assert!(matches!(result,Err(ProgramError::InvalidInstructionData)));\n'
elif family=='place':s+='let r=result.unwrap();assert!(created==Some(r.as_ref() as *const _));assert!(r.as_ref() as *const _!=&request as *const _);\n'
elif family in ['profile','release','program']:
 field={'profile':'verifier_profile','release':'verifier_release','program':'pool_program'}[family]
 s+='let mut r=result.unwrap();'+('r.'+field+'[0]^=1;' if mode=='negative' else '')+'let j:usize=kani::any();kani::assume(j<32);assert!(r.'+field+'[j]==request.'+field+'[j]);\n'
elif family=='arguments':pass
else:
 field=family
 s+='let mut r=result.unwrap();\n'
 if field=='kind':
  if mode=='negative':s+='r.public=match r.public{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)=>PoolV1PairForestTerminalPaymentV1::Withdrawal(any_PoolV1WithdrawalPublicV1()),_=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(any_PoolV1PrivateTransferPublicV1())};\n'
  check=''
 else:
  typ='bytes' if field in ['pool','deployment_domain','destination_token_account'] else 'digest' if field in ['anchor_root','nullifier','recipient_commitment','change_commitment'] else 'scalar' if field=='asset_id' else 'word'
  mutation='[0]^=1' if typ=='bytes' else '[0].0^=1' if typ=='digest' else '.0^=1' if typ=='scalar' else '^=1'
  if mode=='negative':
   s+='match &mut r.public{'
   for v in ['PrivateTransfer','Withdrawal']:
    active=not(field=='recipient_commitment' and v=='Withdrawal') and not(field in ['amount','destination_token_account'] and v=='PrivateTransfer')
    s+='PoolV1PairForestTerminalPaymentV1::'+v+'(p)=>{'+('p.'+field+mutation+';' if active else '')+'},'
   s+='}\n'
  check='let j:usize=kani::any();kani::assume(j<'+('32' if typ=='bytes' else '8')+');assert!(a.FIELD[j]'+('.0' if typ=='digest' else '')+'==b.FIELD[j]'+('.0' if typ=='digest' else '')+');' if typ in ['bytes','digest'] else 'assert!(a.FIELD'+('.0' if typ=='scalar' else '')+'==b.FIELD'+('.0' if typ=='scalar' else '')+');'
  check=check.replace('FIELD',field)
 s+='match (&r.public,&request.public){'
 for v in ['PrivateTransfer','Withdrawal']:
  active=not(field=='recipient_commitment' and v=='Withdrawal') and not(field in ['amount','destination_token_account'] and v=='PrivateTransfer')
  s+='(PoolV1PairForestTerminalPaymentV1::'+v+'(a),PoolV1PairForestTerminalPaymentV1::'+v+'(b))=>{'+(check if active else '')+'},'
 s+='_=>panic!("request variant changed"),}\n'
s+='}\n'
patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);after=f+'\n#[cfg(kani)]\n#[path="NHC_RequestBox.rs"]\nmod NHC_RequestBox;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHC_RequestBox.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NHC_native.patch').write_text(patch);(E/'NHC_CURRENT.json').write_text(json.dumps(dict(kind='source-exact request Box wrapper '+family,mode=mode,source=s,domain='all typed requests and complete nested format-error carrier; borrowed input window length 0..'+str(width)+'; descriptor-parametric production frame not inferred from this bounded window',modifies=['local argument log','fresh allocation/place log'],production_credit=False,error_factories=sorted(made)),indent=1)+'\n')
print('pair_forest::NHC_RequestBox::association')
