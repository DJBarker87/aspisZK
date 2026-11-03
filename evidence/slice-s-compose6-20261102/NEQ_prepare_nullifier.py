from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];assert case in ['statement','payment'] and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_root_window.py'),'9','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
seed=(E/'NEQ_native_contracts.patch').read_text();_,rest=seed.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_window.rs\n',1);raw=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'));body=raw[:raw.index('#[kani::proof]')]
setup='let s=NEE_statement();'
if case=='payment':setup+='let s=match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>PoolV1PairForestTerminalPaymentV1::Withdrawal(public)};'
pattern=['PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}','PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}'] if case=='statement' else ['PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)','PoolV1PairForestTerminalPaymentV1::Withdrawal(public)']
field='anchor_root' if mode=='negative' else 'nullifier'
body+='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn nullifier_getter(){SETUPlet actual=s.nullifier();let expected=match &s{PATTERN=>&public.FIELD};assert!(core::ptr::eq(actual,expected),"same exact borrowed nullifier place and lifetime");}
'''.replace('SETUP',setup).replace('PATTERN=>&public.FIELD',','.join(a+'=>&public.'+field for a in pattern)).replace('FIELD',field)
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_nullifier.rs"]\nmod NEQ_nullifier;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_nullifier.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
impl='PoolV1PairForestTerminalStatementV1' if case=='statement' else 'PoolV1PairForestTerminalPaymentV1';a=f.index('impl '+impl+' {');a=f.index('    pub fn nullifier(',a);z=f.index('\n    }',a)+6;original=f[a:z]
(E/'NEQ_NULLIFIER_CURRENT.json').write_text(json.dumps(dict(case=case,mode=mode,all_typed_inputs=True,canonical_place='public.nullifier in the SAME actual variant',frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),classification='ruling y prime borrowed return; actual getter body, full provenance/place, immutable full carrier; no array-value reduction'),indent=1)+'\n')
