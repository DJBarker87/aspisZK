#!/usr/bin/env python3
"""Verbatim post-zero-scan continuation on actual SDK accounts and carriers."""
from pathlib import Path
import hashlib,json,sys,subprocess
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
base=Path('/tmp/s126-sdk-prefix-v7');s=(base/'src/lib.rs').read_text()
start=s.index('fn stage1(');body=s.index('    let public_data = public_account.try_borrow_data()?;',start)
end=s.index('\npub fn run(',body)
suffix=s[body:end]
replacement='''fn stage1(_program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    // Modular entry: the distinct/metadata/zero-scan prefix has succeeded.
    // The real exclusive guard remains live through this complete suffix.
    let proof_account=&accounts[0];let public_account=&accounts[1];
    let checkpoint_account=&accounts[2];
    let mut checkpoint_data=checkpoint_account.try_borrow_mut_data()?;
'''+suffix
s=s[:start]+replacement+s[end:]
if len(sys.argv)>2 and sys.argv[2]=='after-guards':
 # A second modular cut: the prefix/tag comparisons have already succeeded.
 # Keep the length predicate, checked range, exact first_decoded and writeback.
 s=s.replace('''        || proof_data[..proof_start] != candidate
        || proof_data[proof_start + 8] != Variant::S2.tag()
''','')
 s=s.replace('''// Prefix certificate: argument assertions above occur before this return.
  Err(())''','''if p.fail==4 {Err(())}else{Ok(vec![p.output;p.output_len])}''')
 s=s.replace('''assert!(result.is_err());assert_eq!(after[observed],before);
 assert!(unsafe{CALLS}<=1);kani::cover!(unsafe{CALLS}==1);''','''if result.is_ok(){assert_eq!(unsafe{CALLS},1);assert_eq!(p.output_len,CP);assert_eq!(after[observed],p.output);}
 else {assert_eq!(after[observed],before);}
 assert!(unsafe{CALLS}<=1);kani::cover!(result.is_ok());kani::cover!(unsafe{CALLS}==1 && result.is_err());''')
# The source suffix still checks the candidate prefix and tag. They are not
# silently assumed by replacing those statements in the source.
s=s.replace('fn actual_sdk_stage1_prefix_binding()', 'fn actual_sdk_stage1_tail_binding()')
(O/'src/lib.rs').write_text(s)
c=(base/'Cargo.toml').read_text().replace('aspis-s126-sdk-prefix-boundary','aspis-s126-sdk-tail-boundary')
c=c.replace('/Users/dominic/ZK/.worktrees/s126-caller-20261021','/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src')
(O/'Cargo.toml').write_text(c)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326';path='programs/r1-cost-probe/src/r1_pool_adapter.rs'
source=subprocess.check_output(['git','-C',str(R),'show',freeze+':'+path],text=True)
assert suffix.strip() in source
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=freeze,path=path,suffix=suffix,suffix_sha256=hashlib.sha256(suffix.encode()).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),mode=sys.argv[2:] or ['after-zero'],qualification='Modular stage1 suffix, real SDK borrows/full statement/Public, exact first_decoded body and release None. Entry guards explicitly cut; no whole stage1 claim. after-guards mode omits only prefix/tag comparisons and tests successful checkpoint writeback and child errors. after-zero mode preserves those comparisons but verifier child always Err.'),indent=2)+'\n')
