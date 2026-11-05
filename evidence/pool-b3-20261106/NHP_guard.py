"""Actual transaction-level guard, with unchanged body and cfg(kani) availability."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
reference='pub fn transaction_level(height:usize)->bool { height == 1 }\n'
source='''use super::*;
pub(super) fn reference(height:usize)->ProgramResult {
 let admitted=crate::NHP_reference::transaction_level(height);
 if ADMITTED {Ok(())}else{Err(PoolV1ProgramError::CpiInvocationForbidden.into())}
}
#[kani::proof_for_contract(super::require_transaction_level_invocation_v1)]
fn association(){let height:usize=kani::any();let actual=super::require_transaction_level_invocation_v1(height);assert!(actual==reference(height));}
'''.replace('ADMITTED','admitted' if mode=='positive' else '!admitted')
p='programs/aspis-pool/src/processor.rs';before=read(p)
after=before.replace('#[cfg(any(target_os = "solana", test))]','#[cfg(any(target_os = "solana", test, kani))]')
after=after.replace('fn require_transaction_level_invocation_v1(stack_height: usize)', '#[cfg_attr(kani, kani::ensures(|result| *result == NHP_Guard::reference(stack_height)))]\nfn require_transaction_level_invocation_v1(stack_height: usize)')
after+='\n#[cfg(kani)]\nmod NHP_Guard {\n'+source+'}\n'
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/lib.rs';before=read(p);after=before+'\n#[cfg(any(kani, NHP_extract))]\npub mod NHP_reference;\n'
patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHP_reference.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(reference.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in reference.splitlines())
(E/'NHP_native.patch').write_text(patch);(E/'NHP_reference.rs').write_text(reference)
(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='transaction-level guard',mode=mode,source=source,reference=reference,domain='Every usize stack height; helper body byte-identical; cfg(kani) adds host availability only; does not prove production syscall height or process entry association',modifies=[],production_credit=False,remaining='reference extraction/model law, combined replay/audit/scan; parent entry guard physical association',cfg_availability_change=True),indent=1)+'\n')
print('processor::NHP_Guard::association')
