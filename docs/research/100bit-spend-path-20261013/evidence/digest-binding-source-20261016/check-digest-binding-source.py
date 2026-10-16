from pathlib import Path
import re,hashlib,json
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');raw=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';src=Path('/tmp/TerminalAddDigestBindingSource.lean')
a=raw.read_text();b=src.read_text();entries=[]
for original,local in [('poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK','poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK'),('pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop','add_digest_binding_loop'),('pool_v1.pair_forest_semantic_terminal.add_digest_binding','add_digest_binding')]:
 m=re.search(r'\bdef\s+'+re.escape(original)+r'(?=\s|\()',a);assert m
 end=a.index('\n/-- ',m.start());rawblock=a[m.start():end].strip()
 n=re.search(r'\bdef\s+'+re.escape(local)+r'(?=\s|\()',b);assert n
 ends=[x for x in [b.find('\n/-- ',n.start()),b.find('\nend AspisR1TerminalDigestBindingCandidate',n.start())] if x>=0];localblock=b[n.start():min(ends)].strip()
 renamed=rawblock.replace('pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop','add_digest_binding_loop').replace('pool_v1.pair_forest_semantic_terminal.add_digest_binding','add_digest_binding')
 compact=lambda s:re.sub(r'\s+','',s)
 assert compact(renamed)==compact(localblock),(original,renamed,localblock)
 entries.append({'original':original,'local':local,'raw_def_start_byte':len(a[:m.start()].encode()),'raw_def_end_byte':len(a[:end].encode()),'raw_declaration_sha256':hashlib.sha256(rawblock.encode()).hexdigest(),'local_declaration_sha256':hashlib.sha256(localblock.encode()).hexdigest(),'match':'identical after recorded binding-name shortening and removal of whitespace only'})
Path('/tmp/TerminalAddDigestBindingSource.manifest.json').write_text(json.dumps({'raw_source':str(raw.relative_to(repo)),'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'namespace':'AspisR1TerminalDigestBindingCandidate','declarations':entries},indent=2)+'\n')
print('All three digest source declarations match sealed candidate after name shortening and whitespace only.')
