from pathlib import Path
import hashlib,json,re
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean'
s=p.read_text();prefix='pool_v1.pair_forest_semantic_terminal.';names=['sum_high_loop0_loop0','sum_high_loop0','sum_high'];blocks=[];rows=[]
for name in names:
 full=prefix+name;start=re.search(r'\bdef '+re.escape(full)+r'(?=\s|:)',s).start();doc=s.rfind('/-- ',0,start);end=s.index('\n/-- ',start)
 block=s[doc:end].rstrip()+'\n';blocks.append(block);rows.append({'name':full,'start_byte':len(s[:doc].encode()),'end_byte':len(s[:end].encode()),'retained_sha256':hashlib.sha256(block.encode()).hexdigest()})
header='''import SumHighStdModels

/-! Exact shared source high-selector summation loops and wrapper, retained
byte-for-byte from the sealed generated candidate and isolated by namespace. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1SumHighCandidate
open AspisR1SelectedMaskProbe

'''
out=header+'\n'.join(blocks)+'\nend AspisR1SumHighCandidate\n';q=Path('/tmp/SumHighGeneratedSlice.lean');q.write_text(out)
manifest={'raw_generated_path':str(p.relative_to(repo)),'raw_generated_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declarations':rows,'body_substitutions':{},'explicit_library_model':'SumHighStdModels: namespace-local derived Range.clone, not an external axiom','namespace':'AspisR1SumHighCandidate','module_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path('/tmp/SumHighGeneratedSlice.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(manifest['module_sha256'])
