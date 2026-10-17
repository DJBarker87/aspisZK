from pathlib import Path
import hashlib,json
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');base=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016';f=base/'Funs.lean';t=base/'Types.lean';fs=f.read_text();ts=t.read_text()
name='pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint';a=ts.index('structure '+name+'\n');b=ts.index('\n/--',a);ty=ts[a:b].strip()+'\n';blocks=[]
for name in ['pool_v1.pair_forest_copy_terminal.lift_m31','pool_v1.pair_forest_copy_terminal.accumulate_endpoint']:
 a=fs.index('def '+name+'\n');b=fs.index('\n/--',a);blocks.append(fs[a:b].strip()+'\n')
head='''import SameBoxedRowExact
import TerminalLiftM31Exact
import ExtractedMaskScalarExact
import ArrayUpdateCanonicalExact
import R0P.Copy

/-! Exact endpoint accumulation source and carrier from sealed04fc/60cf.
Shared checked arithmetic and selector owners are imported, not replaced. -/
set_option autoImplicit false
namespace AspisR1CopyEndpointCandidate
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

'''
out=Path('/tmp/CopyEndpointSource.lean');out.write_text(head+ty+'\n'+'\n'.join(blocks)+'\nend AspisR1CopyEndpointCandidate\n');m={'raw_funs_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'raw_types_sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'exact_blocks':True,'carrier_block_sha256':hashlib.sha256(ty.encode()).hexdigest(),'function_block_sha256':[hashlib.sha256(x.encode()).hexdigest() for x in blocks],'relocated_namespace':'AspisR1CopyEndpointCandidate','output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()};Path('/tmp/CopyEndpointSource.manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(m['output_sha256'])
