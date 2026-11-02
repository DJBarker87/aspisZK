"""Ruling y-prime: exact caller cut, provenance-preserving getter oracle."""
from pathlib import Path
import sys,json,subprocess,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose2-20261029';negative=sys.argv[1]=='negative'
patch=(P/'NEE_K052-NEE_native_contracts.patch').read_text().replace('NEE_','NEL_')
oracle=(P/'NEE_K052-NEE_oracle.patch').read_text().replace('NEE_','NEL_')
# Decode added oracle and preserve its frozen caller/reference property.
first,hook=oracle.split('--- a/',1)
body='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n'
body=body.replace(" root:&'a PoolV1PairForestTerminalStatementV1,"," root:&'a PoolV1PairForestTerminalStatementV1,\n pub(super) alternate:&'a PoolV1PairForestTerminalCommonV1,")
body=body.replace('Self{root,payment:', 'Self{root,alternate:root.common(),payment:')
# Inspect the harness before relying on this rewrite.
assert 'fn oracle_domain_positive()' in body,body[-2500:]
body=body.replace('let s=NEL_statement();let mut f=Frame::new(&s);','let s=NEL_statement();let alternate=NEL_common();let mut f=Frame::new(&s);f.alternate=&alternate;')
# Existing root harness exact spelling is checked below.
body=body.replace('let mut frame=Frame::new(&statement);','let mut frame=Frame::new(&statement);frame.alternate=&alternate;')
extra='''
pub(super) fn borrowed_common<'a>(s:&'a PoolV1PairForestTerminalStatementV1, other:&'a PoolV1PairForestTerminalCommonV1)->&'a PoolV1PairForestTerminalCommonV1 {s.common()}
fn designated<'a>(s:&'a PoolV1PairForestTerminalStatementV1, other:&'a PoolV1PairForestTerminalCommonV1)->&'a PoolV1PairForestTerminalCommonV1 { RETURN }
'''.replace('RETURN','other' if negative else 'match s {PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,..}|PoolV1PairForestTerminalStatementV1::Withdrawal{common,..}=>common}')
body=body.replace('#[kani::proof]\n','#[kani::proof]\n#[kani::stub(borrowed_common,designated)]\n')+extra
assert 'f.alternate=&alternate' in body
# Only the cfg(kani) caller copy's getter changes; reference remains actual getter.
patch=patch.replace('+    let common = statement.common();','+    let common = NEL_oracle::borrowed_common(statement,frame.alternate);')
body=body.replace('use super::*;', 'use super::*;\nuse super::pair_forest_terminal::*;\nuse aspis_core::field::M31;\nuse crate::Digest;').replace('super::super::PoolV1PairLiveSnapshotV1','super::PoolV1PairLiveSnapshotV1')
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
patch+=''.join(difflib.unified_diff(frozen.splitlines(True),frozen.replace('use alloc::boxed::Box;','use alloc::boxed::Box;\n#[cfg(kani)]\nuse super::NEL_oracle;').splitlines(True),fromfile='a/'+path,tofile='b/'+path))
# Recompute hunk counts: same number of patch lines; replacement adds no lines.
# Expose the unchanged tuple helper to the sibling oracle reference, scratch only.
needle='fn statement_public_common(' 
patch+=''.join(difflib.unified_diff(frozen.splitlines(True),frozen.replace(needle,'pub(super) '+needle).splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_oracle.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())+'--- a/'+hook)
(E/'NEL_BORROWED_CURRENT.json').write_text(json.dumps(dict(negative=negative,method='ruling y-prime ordinary stub; designated actual field or harness-owned alternate',basis='NEE_K052 unchanged caller assertion, full child Results and local logs',no_stub_verified=True),indent=1)+'\n')
