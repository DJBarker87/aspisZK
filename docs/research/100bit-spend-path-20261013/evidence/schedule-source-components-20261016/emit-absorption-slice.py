from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
base=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016'
rows=[];blocks=[]
prefix='pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal'
names=[('Types.lean',prefix+'.closure'),('Funs.lean','poseidon2.RATE')]+[('Funs.lean',prefix+s) for s in ['.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut','.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once','.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31','.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31','']]
for file,name in names:
 p=base/file;s=p.read_text();m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|:)',s)
 start=m.start();doc=s.rfind('/-- ',0,start);end=s.index('\n/-- ',start)
 block=s[doc:end].rstrip()+'\n';blocks.append(block)
 rows.append({'file':file,'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'name':name,'start_byte':len(s[:doc].encode()),'end_byte':len(s[:end].encode()),'retained_sha256':hashlib.sha256(block.encode()).hexdigest()})
head='''import ArrayFromFnCopySlice
import SelectorValueLaneGeneratedSlice
import SelectedClaimGatherSlice

/-! Exact generated absorption callback, traits and array wrapper. Only the
module framing and isolating namespace are changed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1AbsorptionCandidate
open AspisR1SelectedMaskProbe

'''
out=head+'\n'.join(blocks)+'\nend AspisR1AbsorptionCandidate\n'
p=Path('/tmp/AbsorptionGeneratedSlice.lean');p.write_text(out)
manifest={'raw_directory':str(base.relative_to(repo)),'declarations':rows,'body_substitutions':{},'namespace':'AspisR1AbsorptionCandidate','module_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path('/tmp/AbsorptionGeneratedSlice.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(manifest['module_sha256'])
