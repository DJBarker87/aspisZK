from pathlib import Path
import re,hashlib,json,argparse
parser=argparse.ArgumentParser()
parser.add_argument("--repo",type=Path,required=True)
parser.add_argument("--output",type=Path,required=True)
parser.add_argument("--check",action="store_true")
args=parser.parse_args()
repo=args.repo;b=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016';fs=(b/'Funs.lean').read_text();ts=(b/'Types.lean').read_text()
def block(s,pat):
 m=re.search(pat,s);assert m,pat;return s[m.start():s.index('\n/--',m.start())].strip()+'\n'
width=block(fs,r'@\[global_simps, irreducible\]\ndef poseidon2\.POSEIDON2_WIDTH\b')
ty=block(ts,r'structure pool_v1\.pair_forest_copy_terminal\.CompiledPoolV1PairForestPattern\b')
registry=block(fs,r'@\[global_simps, irreducible\]\ndef pool_v1\.pair_forest_copy_terminal\.constants\.COPY_PATTERNS\b')
# Type ascriptions only: eliminate delayed inference for the unchanged record literal.
raw_registry=registry
registry=registry.replace('  let a :=','  let a : Array Std.U8 16#usize :=')
registry=re.sub(r'  let (a[0-9]+) := Array.repeat 16#usize (0#u(8|32))',lambda m:'  let '+m[1]+' : Array Std.U'+m[3]+' 16#usize := Array.repeat 16#usize '+m[2],registry)
registry=registry.replace('  Array.make 14#usize [','  Array.make 14#usize ([')
assert registry.endswith('    ]\n')
registry=registry[:-len('    ]\n')]+'    ] : List pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern)\n'
# Removing exactly the inserted annotations must reconstruct the sealed block byte for byte.
restored=registry.replace('  let a : Array Std.U8 16#usize :=','  let a :=')
restored=re.sub(r'  let (a[0-9]+) : Array Std.U(8|32) 16#usize :=',r'  let \1 :=',restored)
restored=restored.replace('  Array.make 14#usize ([','  Array.make 14#usize [').replace('    ] : List pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern)\n','    ]\n')
assert restored==raw_registry
count=block(fs,r'@\[global_simps, irreducible\]\ndef\s+pool_v1\.pair_forest_copy_terminal\.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1\b')
helpers=[block(fs,pat) for pat in [r'@\[global_simps, irreducible\]\s+def field\.M31\.ZERO\b',r'@\[global_simps, irreducible\]\s+def field\.CM31\.ZERO\b',r'def field\.CM31\.from_m31\b',r'def field\.QM31\.from_cm31\b',r'def pool_v1\.pair_forest_copy_terminal\.lift_m31\b']]
loop=lambda name:block(fs,r'@\[rust_loop\]\ndef pool_v1\.pair_forest_copy_terminal\.'+name+r'\b')
fn=lambda name:block(fs,r'def pool_v1\.pair_forest_copy_terminal\.'+name+r'\b')
parts=[('CopyPatternPowerSource',['AspisR1SelectedMaskProbe.Funs','Aeneas.Tactic.RustAttributes'],[width,loop('pattern_values_literal_loop0')]),('CopyPatternRegistrySource',['AspisR1SelectedMaskProbe.Funs','Aeneas.Tactic.RustAttributes'],[ty,registry,count]),('CopyPatternLiftSource',['AspisR1SelectedMaskProbe.Funs'],helpers),('CopyPatternInnerSource',['AspisR1.CopyPatternPowerSource','AspisR1.CopyPatternRegistrySource','AspisR1.CopyPatternLiftSource'],[loop('pattern_values_literal_loop1_loop0')]),('CopyPatternOuterSource',['AspisR1.CopyPatternInnerSource'],[loop('pattern_values_literal_loop1')]),('CopyPatternSource',['AspisR1.CopyPatternOuterSource'],[fn('pattern_values_literal'),fn('pattern_values')])]
manifest={'raw_funs_sha256':hashlib.sha256((b/'Funs.lean').read_bytes()).hexdigest(),'raw_types_sha256':hashlib.sha256((b/'Types.lean').read_bytes()).hexdigest(),'namespace':'AspisR1CopyPatternCandidate','exact_blocks_except_explicit_type_ascriptions':True,'raw_registry_sha256':hashlib.sha256(raw_registry.encode()).hexdigest(),'annotated_registry_sha256':hashlib.sha256(registry.encode()).hexdigest(),'registry_annotation_erasure_matches_sealed_block':True,'reason':'Whole declaration bundle was stopped under resource review; compile exact declarations independently to identify the growth, without higher caps or changed function bodies.','partitions':[]}
for name,imports,blocks in parts:
 header=''.join('import '+i+'\n' for i in imports)+'''\n/-! Exact sealed indexed-candidate source partition. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

'''
 text=header+'\n'.join(blocks)+'\nend AspisR1CopyPatternCandidate\n';out=args.output/(name+'.lean');
 if args.check: assert out.read_text()==text,str(out)
 else: out.parent.mkdir(parents=True,exist_ok=True);out.write_text(text)
 manifest['partitions'].append({'module':'AspisR1.'+name,'source_file':out.name,'sha256':hashlib.sha256(text.encode()).hexdigest(),'imports':imports,'block_sha256':[hashlib.sha256(x.encode()).hexdigest() for x in blocks]})
manifest_text=json.dumps(manifest,indent=2)+'\n'
mp=args.output/'manifest.json'
if args.check: assert mp.read_text()==manifest_text
else:mp.write_text(manifest_text)
print(json.dumps(manifest['partitions'],indent=2))
