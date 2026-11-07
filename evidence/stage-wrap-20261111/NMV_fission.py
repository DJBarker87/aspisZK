"""(bn) body-only source fission; PCG_ASSOCIATIONS normalisation method."""
from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def body(s,name):
 m=re.search(r'fn\s+'+name+r'\b',s);assert m,name
 start=s.index('{',m.end());d=1;i=start+1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
norm=lambda s:re.sub(r',(?=[\]})])','',re.sub(r'\s+','',s))
frozen=(E/'NMV_FROZEN_OWNED.rs.txt').read_text()
assert frozen==subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'],text=True)
# Replace CALLS only. Signatures carry abstract descriptors, never RefCell guards.
subs=[('snapshot(', 'W::snapshot(log, '),('stage1_owned(', 'W::stage1_owned(log, '),('stage2_owned(', 'W::stage2_owned(log, '),('program::set_return_data(', 'W::set_return_data(log, '),('Clock::get()', 'W::clock_get(log)'),('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint)', 'W::copy_from_slice(log, W::try_borrow_mut_data(log, &accounts[2])?, &checkpoint)')]
# Rust forbids two overlapping &mut borrows of log in one call; use a
# guard-free handle method taking the independent log after acquisition.
subs[-1]=('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint)', 'W::try_borrow_mut_data(log, &accounts[2])?.copy_from_slice(log, &checkpoint)')
header='''// NMV source-fission descriptors. Window laws are interpreted in Lean.
#![allow(non_upper_case_globals)]
pub type Pubkey = [u8;32];
pub type ProgramResult = Result<(),ProgramError>;
pub struct Clock { pub slot: u64 }
'''
err=(E.parent/'pc-helpers2-20261110/PCG_solana_program_error.rs.txt').read_text()
header+=err[err.index('pub enum ProgramError'):err.index('\nimpl std::error::Error')]+'\n'
header+='''pub trait WriteWindow<L> { fn copy_from_slice(self, log: &mut L, source: &[u8]); }
pub trait Windows: Sized {
    type Account;
    type Owned;
    type Write: WriteWindow<Self>;
    fn snapshot(log: &mut Self, account: &Self::Account, length1: usize, length2: usize) -> Self::Owned;
    fn stage1_owned(log: &mut Self, program: &Pubkey, accounts: &[Self::Owned], data: &[u8]) -> Result<Vec<u8>,ProgramError>;
    fn stage2_owned(log: &mut Self, program: &Pubkey, accounts: &[Self::Owned], data: &[u8], slot: Result<u64,ProgramError>) -> ProgramResult;
    fn try_borrow_mut_data(log: &mut Self, account: &Self::Account) -> Result<Self::Write,ProgramError>;
    fn set_return_data(log: &mut Self, data: &[u8]);
    fn clock_get(log: &mut Self) -> Result<Clock,ProgramError>;
}
'''
# Pin these against the RSL constant audit and frozen source provenance.
constants={'POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES':688,'POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES':1880,'CHECKPOINT_TAIL_BYTES':1768,'POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES':384,'POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES':192,'POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES':768,'POOL_V1_VERIFIER_REGISTRY_BYTES':128,'POOL_V1_VERIFIER_REGISTRY_V2_BYTES':256,'POOL_V1_VERIFIER_ENTRY_BYTES':192,'POOL_V1_VERIFIER_ENTRY_V2_BYTES':320}
header+='pub mod verifier { pub const PROOF_BYTES: usize = 57607; }\n'
for k,v in constants.items():header+=f'pub const {k}: usize = {v};\n'
header+='pub const POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC: [u8;4] = *b"ASQ8";\n'
results=[];out=header
for name,row in [('stage2','TX2:240'),('stage1','TX1:344')]:
 actual=body(frozen,name);copy=actual
 for a,b in subs:copy=copy.replace(a,b)
 erased=copy
 for a,b in reversed(subs):erased=erased.replace(b,a)
 assert norm(actual)==norm(erased),(row,'fission erasure mismatch')
 out+=f'pub fn {name}<W: Windows>(log: &mut W, program_id: &Pubkey, accounts: &[W::Account], data: &[u8]) -> ProgramResult '+copy+'\n'
 results.append(dict(row=row,frozen_sha256=sha(actual.encode()),fission_sha256=sha(copy.encode()),transforms=[(b,a) for a,b in reversed(subs) if b in copy],exact_after_whitespace_and_optional_trailing_commas=True))
(E/'NMV_Fission.rs').write_text(out)
(E/'NMV_ASSOCIATIONS.json').write_text(json.dumps(results,indent=2)+'\n')
print('Both stage fission bodies erase exactly to frozen bodies')
