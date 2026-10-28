from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
s=(E/'NBX_slots.rs.txt').read_text();attrs=re.search(r'#\[kani::proof\].*?#\[kani::unwind\(33\)\]\n',s,re.S).group()
items=[]
def harness(name,body,condition):
 global s
 for neg in [False,True]:
  n=name+('_negative' if neg else '')
  s+=attrs+'fn NBX_'+n+'(){'+body+'\nassert!('+('!(' if neg else '(')+condition+'));}\n'
  items.append(('pool_v1::verifier_registry::NBX_slots::NBX_'+n,neg))
for op,n,fn in [(31,128,'decode_verifier_registry_v1'),(32,192,'decode_verifier_registry_entry_v1'),(33,256,'decode_verifier_registry_v2'),(34,320,'decode_verifier_registry_entry_v2')]:
 harness('op'+str(op)+'_arguments',f'let a:[u8;{n}]=kani::any();let j:usize=kani::any();kani::assume(j<{n});let before=a[j];let x={fn}(&a);let y={fn}(&a);', 'x==y && a[j]==before')
f='crate::pool_v1::format::'
harness('op15_arguments','let p='+f+'VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()};let j:usize=kani::any();kani::assume(j<32);let old=p.registry_program[j];let x='+f+'validate_verifier_policy_v1(&p);let y='+f+'validate_verifier_policy_v1(&p);','x==y && p.registry_program[j]==old')
for name,n in [('identity',144),('policy',104)]:
 fn=f+'decode_'+('pool_identity_v1' if name=='identity' else 'verifier_policy_v1')
 harness(name+'_arguments',f'let a:[u8;{n}]=kani::any();let j:usize=kani::any();kani::assume(j<{n});let old=a[j];let x={fn}(&a);let y={fn}(&a);','x==y && a[j]==old')
f='crate::pool_v1::pair_forest_terminal::'
harness('op23_magic_frame','let a:[u8;320]=kani::any();kani::assume(a[0]!=65);let j:usize=kani::any();kani::assume(j<320);let old=a[j];let x='+f+'decode_pool_v1_pair_forest_terminal_request_v1(&a);','x==Err('+f+'PoolV1PairForestTerminalFormatErrorV1::WrongMagic) && a[j]==old')
# Native one-iteration cuts; no entire sequence-array/iterator replay.
s+='''fn NBX_master_step(bytes:&[u8;384],out:&mut [u64;8],lane:usize){let start=320+8*lane;out[lane]=u64::from_le_bytes(bytes[start..start+8].try_into().unwrap());}
fn NBX_checkpoint_step(bytes:&[u8;192],out:&mut [u64;8],lane:usize)->bool {let start=112+8*lane;out[lane]=u64::from_le_bytes(bytes[start..start+8].try_into().unwrap());out[lane]>1048576}
'''
for name,n,start in [('master',384,320),('checkpoint',192,112)]:
 b=f'let bytes:[u8;{n}]=kani::any();let mut out:[u64;8]=kani::any();let lane:usize=kani::any();let j:usize=kani::any();kani::assume(lane<8 && j<8);let old=out[j];let k={start}+8*lane;let value=u64::from_le_bytes([bytes[k],bytes[k+1],bytes[k+2],bytes[k+3],bytes[k+4],bytes[k+5],bytes[k+6],bytes[k+7]]);'
 b+='let bad=NBX_checkpoint_step(&bytes,&mut out,lane);' if name=='checkpoint' else 'NBX_master_step(&bytes,&mut out,lane);'
 harness(name+'_iteration',b,'out[j]==(if j==lane {value}else{old})'+(' && bad==(value>1048576)' if name=='checkpoint' else ''))
harness('reserved_iteration','let before:bool=kani::any();let byte:u8=kani::any();let next=if before {true}else{byte!=0};','next==(before || byte!=0)')
for name,n,start,end in [('request',320,104,320),('master_identity',384,64,208)]:
 harness(name+'_window',f'let a:[u8;{n}]=kani::any();let k:usize=kani::any();kani::assume(k<{end-start});let window=&a[{start}..{end}];','window.len()=='+str(end-start)+f' && window[k]==a[{start}+k]')
(E/'NBX_slots.rs.txt').write_text(s)
(E/'NBX_MORE_SEQUENCE.json').write_text(json.dumps(items,indent=2)+'\n')
