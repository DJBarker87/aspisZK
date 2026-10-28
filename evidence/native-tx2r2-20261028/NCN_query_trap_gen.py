from NCN_extend import E,current
import difflib,json
s=current();t=s
start=s.index('#[cfg(kani)] mod NCN_resume')
part=s[start:]
for name in ['query_range_ok','query_range_wrong']:
 part=part.replace('fn '+name+'()', '#[kani::stub(<[u32]>::contains,contains_never)]\nfn '+name+'()')
part=part.replace('use core::cell::Cell;','use core::cell::Cell;\nfn contains_never(_: &[u32],_: &u32)->bool {assert!(false,"unreachable contains call");false}')
t=s[:start]+part
(E/'NCN_query_trap.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs')))
(E/'NCN_query_trap_queue.json').write_text(json.dumps([dict(attempt=f'NCN_K{i:03}',harness='verifier::NCN_resume::'+name,negative=neg,patch='NCN_query_trap.patch') for i,name,neg in [(75,'query_range_ok',False),(76,'query_range_wrong',True)]],indent=2)+'\n')
