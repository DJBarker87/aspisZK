from pathlib import Path
import re,hashlib,json
b=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016');f=b/'Funs.lean';s=f.read_text()
def block(pat):
 m=re.search(pat,s);assert m;end=s.index('\n/--',m.start());return s[m.start():end].strip()+'\n'
blocks=[block(r'@\[global_simps, irreducible\]\ndef pool_v1\.pair_forest_copy_terminal\.constants\.COPY_LINKS\b'),block(r'@\[global_simps, irreducible\]\ndef\s+pool_v1\.pair_forest_copy_terminal\.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1\b'),block(r'@\[rust_loop\]\ndef pool_v1\.pair_forest_copy_terminal\.evaluate_with_selectors_loop\b')]
ns='pool_v1.pair_forest_copy_terminal.'
mapping={ns+'CompiledPoolV1PairForestLink':'AspisR1CopyLinkWeightCandidate.'+ns+'CompiledPoolV1PairForestLink',ns+'PoolV1PairForestCompiledVariantV1':'AspisR1CopyLinkWeightCandidate.'+ns+'PoolV1PairForestCompiledVariantV1',ns+'link_weight':'AspisR1CopyLinkWeightCandidate.'+ns+'link_weight',ns+'accumulate_endpoint':'AspisR1CopyEndpointCandidate.'+ns+'accumulate_endpoint'}
adapted=[]
for raw in blocks:
 text=raw
 for a,z in mapping.items():text=text.replace(a,z)
 inv=text
 for a,z in mapping.items():inv=inv.replace(z,a)
 assert inv==raw
 adapted.append(text)
header='''import CopyLinkWeightSource

/-! Exact sealed candidate registry and 136-link loop. Shared descriptor,
weight and endpoint declaration owners are named explicitly by an invertible map. -/
set_option autoImplicit false
namespace AspisR1CopyLinkLoopCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

'''
out=Path('/tmp/CopyLinkLoopSource.lean');out.write_text(header+'\n'.join(adapted)+'\nend AspisR1CopyLinkLoopCandidate\n');manifest={'raw_funs_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'raw_blocks_sha256':[hashlib.sha256(x.encode()).hexdigest() for x in blocks],'explicit_owner_map':mapping,'inverse_owner_map_checked':True,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()};Path('/tmp/CopyLinkLoopSource.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(manifest['output_sha256'])
