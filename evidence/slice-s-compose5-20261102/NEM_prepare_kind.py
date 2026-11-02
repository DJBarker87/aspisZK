"""Actual typed getters and parser at their caller byte windows; no loop or copy."""
from pathlib import Path
import subprocess,difflib,json,sys
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];assert case in ['statement','payment','parse'];assert mode in ['positive','wrong_value','wrong_place','wrong_receiver']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
old=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();added='\n'.join(l[1:] for l in old.splitlines() if l.startswith('+') and not l.startswith('+++'));a=added.index('fn NEE_digest()');z=added.index('\n\n',added.index('fn NEE_statement()'));construct=added[a:z]
body='use super::*;\nuse aspis_core::field::M31;\n'+construct+'\n#[kani::proof]\nfn kind_call(){\n'
if case=='parse':
 body+='let bytes:[u8;320]=kani::any();let byte=bytes[5];let actual=transition_kind(bytes[INDEX]);let expected=if byte==1{Ok(PoolV1TransitionKind::PrivateTransfer)}else if byte==2{Ok(PoolV1TransitionKind::Withdrawal)}else{Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)};assert!(ACTUAL==expected,"same byte and full parser Result including every invalid byte");\n'
 body=body.replace('INDEX','6' if mode=='wrong_place' else '5').replace('ACTUAL','transition_kind(byte^3)' if mode=='wrong_value' else 'actual')
else:
 body+='let s=NEE_statement();let expected=match &s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}=>1u8,PoolV1PairForestTerminalStatementV1::Withdrawal{..}=>2u8};\n'
 if case=='payment':body+='let p=match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>PoolV1PairForestTerminalPaymentV1::Withdrawal(public)};let kind=p.transition_kind();\n'
 else:body+='let kind=s.transition_kind();\n'
 body+='let mut output:[u8;1880]=kani::any();let j:usize=kani::any();kani::assume(j<1880);let old=output[j];output[INDEX]=VALUE;assert!(output[j]==if j==5{expected}else{old},"same kind result and complete scalar write frame");\n'
 body=body.replace('INDEX','6' if mode=='wrong_place' else '5').replace('VALUE','(kind as u8)^3' if mode=='wrong_value' else ('3-(kind as u8)' if mode=='wrong_receiver' else 'kind as u8'))
body+='}\n'
changed=f+'\n#[cfg(kani)]\n#[path="NEM_kind_call.rs"]\nmod NEM_kind_call;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_kind_call.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_KIND_CURRENT.json').write_text(json.dumps(dict(case=case,mode=mode,all_typed_inputs=True,no_acceptance_precondition=True,actual_call=True,same_call_byte=5,arbitrary_prestate=True,no_copy_or_loop=True,classification='typed enum projection at caller scalar window' if case!='parse' else 'all-u8 parser at SAME request byte, complete Result'),indent=1)+'\n')
