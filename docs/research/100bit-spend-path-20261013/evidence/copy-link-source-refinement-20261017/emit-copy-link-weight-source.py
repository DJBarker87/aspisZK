from pathlib import Path
import re,hashlib,json
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');b=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016';f=b/'Funs.lean';t=b/'Types.lean';fs=f.read_text();ts=t.read_text()
def block(s,pattern):
 m=re.search(pattern,s);assert m;start=m.start();end=s.index('\n/--',start);return s[start:end].strip()+'\n'
tyVariant=block(ts,r'@\[discriminant isize\]\ninductive pool_v1\.pair_forest_copy_terminal\.PoolV1PairForestCompiledVariantV1\b')
tyLink=block(ts,r'structure pool_v1\.pair_forest_copy_terminal\.CompiledPoolV1PairForestLink\b')
old='pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint';new='AspisR1CopyEndpointCandidate.'+old;adaptedLink=tyLink.replace(old,new);assert adaptedLink.replace(new,old)==tyLink
funEq=block(fs,r'def\s+pool_v1\.pair_forest_copy_terminal\.PoolV1PairForestCompiledVariantV1\.Insts\.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1\.eq\b')
one=block(fs,r'@\[global_simps, irreducible\] def field\.M31\.ONE\b')
funWeight=block(fs,r'def pool_v1\.pair_forest_copy_terminal\.link_weight\b')
header='''import Aeneas
import CopyEndpointSource
import CopyLinkBitArithmetic

/-! Exact link-weight source and source descriptor. Endpoint carrier is the
same prior exact source owner; inverse type-name map is retained. -/
set_option autoImplicit false
namespace AspisR1CopyLinkWeightCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

'''
out=Path('/tmp/CopyLinkWeightSource.lean');out.write_text(header+'\n'.join([tyVariant,adaptedLink,funEq,one,funWeight])+'\nend AspisR1CopyLinkWeightCandidate\n');m={'raw_funs_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'raw_types_sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'raw_block_sha256':{'variant':hashlib.sha256(tyVariant.encode()).hexdigest(),'link':hashlib.sha256(tyLink.encode()).hexdigest(),'variant_eq':hashlib.sha256(funEq.encode()).hexdigest(),'m31_one':hashlib.sha256(one.encode()).hexdigest(),'link_weight':hashlib.sha256(funWeight.encode()).hexdigest()},'endpoint_type_substitution':{old:new},'inverse_type_map_checked':True,'relocated_namespace':'AspisR1CopyLinkWeightCandidate','output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()};Path('/tmp/CopyLinkWeightSource.manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(m['output_sha256'])
