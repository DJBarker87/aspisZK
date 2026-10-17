from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');base=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016';f=base/'Funs.lean';t=base/'Types.lean';fs=f.read_text();ts=t.read_text()
fn='pool_v1.pair_forest_copy_terminal.copy_residual';ty='pool_v1.pair_forest_copy_terminal.CopyRowExtension'
a=fs.index('def '+fn+'\n');b=fs.index('\n/--',a);rawfun=fs[a:b].strip()+'\n';c=ts.index('structure '+ty+' where');d=ts.index('\n/--',c);rawtype=ts[c:d].strip()+'\n'
header='''import EqualityValueAdapter
import ExtractedMaskHornerStep
import R0P.Copy

/-! Exact generated copy-residual function and row carrier. Source cut only;
pattern/link accumulation and whole evaluate_with_selectors are separate. -/
set_option autoImplicit false
namespace AspisR1CopyResidualCandidate
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

'''
out=Path('/tmp/CopyResidualSource.lean');out.write_text(header+rawtype+'\n'+rawfun+'\nend AspisR1CopyResidualCandidate\n');Path('/tmp/CopyResidualSource.manifest.json').write_text(json.dumps({'raw_funs_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'raw_types_sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'declaration':fn,'carrier':ty,'function_block_sha256':hashlib.sha256(rawfun.encode()).hexdigest(),'carrier_block_sha256':hashlib.sha256(rawtype.encode()).hexdigest(),'exact_declaration_blocks':True,'relocated_namespace':'AspisR1CopyResidualCandidate','helper_owners':'AspisR1SelectedMaskProbe','source_only_no_behavior_claim':True,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()},indent=2)+'\n');print(hashlib.sha256(out.read_bytes()).hexdigest())
