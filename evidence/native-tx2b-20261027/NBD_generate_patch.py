from pathlib import Path
import subprocess,difflib,json,hashlib
E=Path('evidence/native-tx2b-20261027');rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';root='crates/aspis-statement/src/pool_v1/'
registry='''// Scratch-only native getter gate. All control fields and slots arbitrary.
use super::*;
#[kani::proof]
fn NBD_registry_getters() {
    let flags: u8 = kani::any();
    let status_byte: u8 = kani::any();
    let activation: u64 = kani::any();
    let retirement: u64 = kani::any();
    let slot: u64 = kani::any();
    let parsed = VerifierEntryStatusV1::try_from(status_byte);
    assert_eq!(parsed, match status_byte {
        0 => Ok(VerifierEntryStatusV1::Pending),
        1 => Ok(VerifierEntryStatusV1::Active),
        2 => Ok(VerifierEntryStatusV1::Paused),
        3 => Ok(VerifierEntryStatusV1::Retired),
        _ => Err(PoolV1VerifierRegistryFormatError::InvalidStatus),
    });
    let status = match parsed { Ok(s) => s, Err(_) => return };
    let v1 = VerifierRegistryV1 { flags, bump:0,pool:[0;32],authority:[0;32],policy_binding:[0;32],generation:0,minimum_activation_delay_slots:0 };
    let v2 = VerifierRegistryV2 { flags,bump:0,pool:[0;32],authority:[0;32],policy_binding:[0;32],generation:0,minimum_activation_delay_slots:0,registry_program:[0;32],loader_program:[0;32],programdata_address:[0;32],programdata_bump:0,executable_hash:[0;32] };
    assert_eq!(v1.is_paused(), flags % 2 == 1);
    assert_eq!(v2.is_paused(), flags % 2 == 1);
    assert_eq!(v1.is_immutable(), (flags / 2) % 2 == 1);
    assert_eq!(v2.is_immutable(), (flags / 2) % 2 == 1);
    let e1 = VerifierRegistryEntryV1 {status,statement_version:0,bump:0,pool:[0;32],verifier_program:[0;32],profile_binding:[0;32],release_binding:[0;32],activation_slot:activation,retirement_slot:retirement,policy_binding:[0;32]};
    let e2 = VerifierRegistryEntryV2 {status,statement_version:0,bump:0,pool:[0;32],verifier_program:[0;32],profile_binding:[0;32],release_binding:[0;32],activation_slot:activation,retirement_slot:retirement,policy_binding:[0;32],loader_program:[0;32],programdata_address:[0;32],programdata_bump:0,executable_hash:[0;32],expected_upgrade_authority:[0;32]};
    let no_retire = retirement == u64::MAX;
    let active = status_byte == 1 && activation <= slot && (no_retire || slot < retirement);
    assert_eq!(e1.has_no_retirement_slot(), no_retire);
    assert_eq!(e2.has_no_retirement_slot(), no_retire);
    assert_eq!(e1.is_active_at(slot), active);
    assert_eq!(e2.is_active_at(slot), active);
}
'''
# Mechanical one-iteration probe; source loop is not run wholesale.
src=subprocess.check_output(['git','show',rev+':'+root+'pair_tree_profile.rs'],text=True)
start=src.index('    while i < value.len() {',src.index('pub(crate) fn digest_is_canonical'))
end=src.index('    true\n}',start)
loop=src[start:end]
expected='''    while i < value.len() {
        if value[i].0 >= P {
            return false;
        }
        i += 1;
    }
'''
assert loop==expected
probe=loop.replace('while i < value.len()', 'if i < value.len()').replace('return false;', 'return (false, i, true);')
digest='''// Frozen loop body, with while replaced by one if and explicit exit state.
use super::*;
fn NBD_native_iteration(value: &Digest, mut i: usize) -> (bool, usize, bool) {
'''+probe+'''    (true, i, i == value.len())
}
#[kani::proof]
fn NBD_digest_iteration() {
    let words: [u32;8] = kani::any();
    let value = words.map(M31);
    let i: usize = kani::any();
    kani::assume(i <= 8);
    let result = NBD_native_iteration(&value, i);
    let expected = if i == 8 { (true, i, true) }
        else if words[i] >= 2147483647 { (false, i, true) }
        else { (true, i + 1, i + 1 == 8) };
    assert_eq!(result, expected);
}
'''
registry=registry.replace(':0',':kani::any()').replace(':[0;32]',':kani::any()')
# Full arbitrary typed inputs for the getter-only terminal gate; no native codec loop.
def frozen(file): return subprocess.check_output(['git','show',rev+':'+root+file],text=True)
def ctor(ty):
    if ty in ['u8','u32','u64','[u8; 32]']: return 'kani::any()'
    if ty=='M31': return 'M31(kani::any())'
    if ty=='Digest': return '['+','.join('M31(kani::any())' for _ in range(8))+']'
    if ty=='[Digest; super::POOL_V1_PAIR_TREE_DEPTH]': return '['+','.join(ctor('Digest') for _ in range(20))+']'
    if ty=='[Digest; POOL_V1_PAIR_TREE_DEPTH]': return '['+','.join(ctor('Digest') for _ in range(20))+']'
    owners={'PoolV1PrivateTransferPublicV1':'payment_relation.rs','PoolV1WithdrawalPublicV1':'payment_relation.rs','PoolV1PairVerifiedAfterstateV1':'pair_terminal.rs','PoolV1PairLiveSnapshotV1':'pair_tree_profile.rs','PoolV1PairLatePublicStatementV1':'pair_tree_profile.rs','PoolV1PairForestTerminalCommonV1':'pair_forest_terminal.rs'}
    import re
    body=frozen(owners[ty]).split('pub struct '+ty+' {',1)[1].split('\n}',1)[0]
    fields=re.findall(r'^    pub (\w+): ([^\n]+),$',body,re.M)
    assert fields,(ty,body)
    return 'crate::pool_v1::'+ty+' {'+','.join(name+':'+ctor(kind) for name,kind in fields)+'}'
terminal='use super::*;\n#[kani::proof]\nfn NBD_terminal_getters() {\n'
terminal+='    let transfer = '+ctor('PoolV1PrivateTransferPublicV1')+';\n'
terminal+='    let withdrawal = '+ctor('PoolV1WithdrawalPublicV1')+';\n'
terminal+='    let common = '+ctor('PoolV1PairForestTerminalCommonV1')+';\n'
terminal+='''    let choose: bool = kani::any();
    let (s,p,kind,n,pool,deployment,seq,anchor,asset) = if choose {
      (PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public: transfer }, PoolV1PairForestTerminalPaymentV1::PrivateTransfer(transfer),PoolV1TransitionKind::PrivateTransfer,transfer.nullifier,transfer.pool,transfer.deployment_domain,transfer.anchor_sequence,transfer.anchor_root,transfer.asset_id)
    } else {
      (PoolV1PairForestTerminalStatementV1::Withdrawal { common, public: withdrawal },PoolV1PairForestTerminalPaymentV1::Withdrawal(withdrawal),PoolV1TransitionKind::Withdrawal,withdrawal.nullifier,withdrawal.pool,withdrawal.deployment_domain,withdrawal.anchor_sequence,withdrawal.anchor_root,withdrawal.asset_id)
    };
    let common_ref = match &s { PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,..} | PoolV1PairForestTerminalStatementV1::Withdrawal{common,..} => common };
    let nullifier_ref = match &s { PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..} => &public.nullifier, PoolV1PairForestTerminalStatementV1::Withdrawal{public,..} => &public.nullifier };
    let payment_ref = match &p { PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => &public.nullifier, PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => &public.nullifier };
    assert!(core::ptr::eq(s.common(),common_ref));
    assert!(core::ptr::eq(s.nullifier(),nullifier_ref));
    assert!(core::ptr::eq(p.nullifier(),payment_ref));
    assert_eq!(*s.common(),common);
    assert_eq!(s.transition_kind(),kind);
    assert_eq!(*s.nullifier(),n);
    assert_eq!(p.transition_kind(),kind);
    assert_eq!(*p.nullifier(),n);
    assert_eq!(statement_public_common(&s),(pool,deployment,seq,anchor,n,asset));
    let byte: u8 = kani::any();
    assert_eq!(transition_kind(byte),match byte { 1=>Ok(PoolV1TransitionKind::PrivateTransfer),2=>Ok(PoolV1TransitionKind::Withdrawal),_=>Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind) });
}
'''
files={root+'NBD_registry.rs':registry,root+'NBD_digest.rs':digest,root+'NBD_terminal.rs':terminal}
patch=''
for file,child in [('verifier_registry.rs','NBD_registry'),('pair_tree_profile.rs','NBD_digest'),('pair_forest_terminal.rs','NBD_terminal')]:
 p=root+file;old=subprocess.check_output(['git','show',rev+':'+p],text=True);new=old+'\n#[cfg(kani)]\n#[path="'+child+'.rs"]\nmod '+child+';\n'
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
for p,new in files.items():patch+=''.join(difflib.unified_diff([],new.splitlines(True),fromfile='/dev/null',tofile='b/'+p))
(E/'NBD_harness.patch').write_text(patch)
(E/'NBD_NATIVE_STEP.json').write_text(json.dumps(dict(revision=rev,frozen_loop=loop,frozen_loop_sha256=hashlib.sha256(loop.encode()).hexdigest(),probe=probe,transformation='while to if; return false to explicit done(false,index); valid fallthrough retains i+=1; invariant 0<=i<=8. Completion marker after increment is a probe summary, not an extra source branch.'),indent=2)+'\n')
