from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';src=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode()
start=src.index('fn validate_transition(');idx=src.index('{',start)+1;i=idx;depth=1
while depth:
 if src[i]=='{':depth+=1
 if src[i]=='}':depth-=1
 i+=1
body=src[idx:i-1];opening=body[:body.index('    for level in 0..20 {')];old='bounded_append_carry(index)';new='carry_cut(index,log)';assert opening.count(old)==1;changed=opening.replace(old,new);assert changed.replace(new,old)==opening
(E/'NHU_transition_header_body.rs.txt').write_text('fn NHU_transition_header_cut(public:SemanticPublic,log:&mut CarryLog)->Result<(u64,usize),PoolV1PairForestSemanticTerminalErrorV1>{'+changed+'\nOk((index,carry))\n}\n')
loop=body[body.index('    for level in 0..20 {')+len('    for level in 0..20 {'):];loop=loop[:loop.rindex('\n    }')];assert loop.count('continue;')==1;changed=loop.replace('continue;','return Ok(iter.start);');assert changed.replace('return Ok(iter.start);','continue;')==loop
(E/'NHU_transition_step_body.rs.txt').write_text('fn NHU_transition_step_cut(public:SemanticPublic,carry:usize,level:usize)->Result<usize,PoolV1PairForestSemanticTerminalErrorV1>{let source=public.transition.live_snapshot;let after=public.transition.candidate_afterstate;let index=source.next_pair_index;let mut iter=level..20;if let Some(level)=iter.next(){'+changed+'\n}\nOk(iter.start)\n}\n')
(E/'NHU_TRANSITION_ERASURE.json').write_text(json.dumps(dict(status='PASS',revision=rev,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),header_sha256=hashlib.sha256(opening.encode()).hexdigest(),loop_sha256=hashlib.sha256(loop.encode()).hexdigest(),substitutions=[[old,new],['continue;','return Ok(iter.start);']],method='one real forward-Range iteration on arbitrary prestate; exact frozen header; full raw typed immutable Public/transition; only carry child is a local-record oracle'),indent=1)+'\n')
