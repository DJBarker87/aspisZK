from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();name='pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop';m=re.search(r'\bdef '+re.escape(name)+r'\s',s);a=m.start();b=s.index('\n/-- ',a);raw=s[a:b].strip()
out=Path('/tmp/TerminalDigestPublicLoopSource.lean');q=out.read_text();x=q.index('def public_digest_lanes_loop');y=q.index('\nend ',x);body=q[x:y].strip()
subs={'AspisR1TerminalDigestBindingCandidate.add_digest_binding':'pool_v1.pair_forest_semantic_terminal.add_digest_binding','AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root':'pool_v1.pair_forest_semantic_terminal.empty_root','AspisR1AbsorptionCandidate.poseidon2.RATE':'poseidon2.RATE'}
restored=body
for old,new in subs.items():restored=restored.replace(old,new)
restored=re.sub(r'\bpublic_digest_lanes_loop\b',name,restored)
assert ''.join(raw.split())==''.join(restored.split())
manifest={'raw_source':str(p.relative_to(repo)),'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declaration':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'raw_block_sha256':hashlib.sha256(raw.encode()).hexdigest(),'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'inverse_helper_substitutions':subs,'inverse_self_qualification':name,'token_stream_equal_ignoring_whitespace':True,'body_modifications':[]}
Path('/tmp/TerminalDigestPublicLoopSource.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('Original outer-loop token stream verified after inverse helper qualification; no body modifications.')
