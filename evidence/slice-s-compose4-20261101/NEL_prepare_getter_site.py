"""Split the first frozen caller statement, retaining actual borrow provenance."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose2-20261029';negative=sys.argv[1]=='negative'
# Reuse only unchanged arbitrary constructors, never an old semantic verdict.
p=(P/'NEE_K005-NEE_oracle.patch').read_text();first,hook=p.split('--- a/',1)
body='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n'
body=body[:body.index('#[derive(Clone,Copy,Debug,PartialEq,Eq)]')].replace('NEE_','NEL_')
body=body.replace('use super::*;','use super::*;\nuse super::pair_forest_terminal::*;\nuse aspis_core::field::M31;\nuse crate::Digest;').replace('super::super::PoolV1PairLiveSnapshotV1','super::PoolV1PairLiveSnapshotV1')
body+='''
fn borrow_target<'a>(s:&'a PoolV1PairForestTerminalStatementV1, other:&'a PoolV1PairForestTerminalCommonV1)->&'a PoolV1PairForestTerminalCommonV1{s.common()}
fn designated<'a>(s:&'a PoolV1PairForestTerminalStatementV1, other:&'a PoolV1PairForestTerminalCommonV1)->&'a PoolV1PairForestTerminalCommonV1{RETURN}
fn caller_site<'a>(statement:&'a PoolV1PairForestTerminalStatementV1, other:&'a PoolV1PairForestTerminalCommonV1)->&'a PoolV1PairForestTerminalCommonV1{
 let common = borrow_target(statement,other);
 common
}
#[kani::proof]
#[kani::stub(borrow_target,designated)]
fn getter_site(){let s=NEL_statement();let other=NEL_common();let actual=caller_site(&s,&other);let expected=match &s {PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,..}|PoolV1PairForestTerminalStatementV1::Withdrawal{common,..}=>common};assert!(core::ptr::eq(actual,expected),"same borrowed place at validator getter call");}
'''.replace('RETURN','other' if negative else 'match s {PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,..}|PoolV1PairForestTerminalStatementV1::Withdrawal{common,..}=>common}')
(E/'NEL_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_oracle.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())+'--- a/'+hook.replace('NEE_','NEL_'))
(E/'NEL_native_contracts.patch').write_text('')
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=frozen.index('pub fn validate_pool_v1_pair_forest_terminal_statement_v1(');assert '    let common = statement.common();' in frozen[a:a+200]
(E/'NEL_GETTER_SITE_CURRENT.json').write_text(json.dumps(dict(source=path,first_frozen_statement='let common = statement.common();',frozen_source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),negative=negative,ordinary_stub=True,borrow_provenance='actual common field in the actual receiver',wrong_place_control='disjoint harness-owned Common',scope='single first callsite statement, no native whole-root claim'),indent=1)+'\n')
