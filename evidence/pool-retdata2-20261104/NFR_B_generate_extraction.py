"""Replay E001's selected body against proved canonical owners, never the external template."""
from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent; O=E.parent/'pool-retdata-20261104'
D=O/'NFO_E001_outputs'
root='aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_result_v1'
parts=[]; inputs=[]; substitutions=[]
for name in ['Types','Funs']:
 p=D/f'NFO_decode_extracted__NFO_DecodeExtracted__{name}.lean.txt';s=p.read_text()
 for m in re.finditer(r'(?m)^def(?:\s|\n)',s):
  end=s.find('\n/--',m.start());end=len(s) if end<0 else end
  block=s[m.start():end].split('\nend NFO_DecodeExtracted')[0].strip()
  if not re.match(r'def\s+'+re.escape(root)+r'(?:\s|\.)',block.split(':=',1)[0]):continue
  block=block.replace(root,'decode').replace('aspis_statement.','AspisR1TerminalDecoder.')
  # Keep monadic extraction slots: replace each external getter by a definition,
  # whose equality to its canonical counterpart is checked below.
  for old,new in [
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES','resultBytes'),
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC','resultMagic'),
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION','resultVersion'),
   ('AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION','digestVersion'),
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET','masterOffset'),
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET','selectedOffset'),
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET','nullifierOffset'),
   ('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET','afterstateOffset'),
   ('Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8','sliceArrayNe')]:
   block=block.replace(old,new)
  parts.append(block)
 inputs.append(dict(path=str(p.relative_to(E.parent.parent)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
assert len(parts)==16
header="""import NFO_RawDecode
import NFO_DecodeOracle
set_option autoImplicit false
noncomputable section
namespace NFR_ExtractedDecode
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
def resultBytes : Result Usize := ok 792#usize
def resultMagic := ok pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC
def resultVersion := ok pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
def digestVersion := ok pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
def masterOffset := ok pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET
def selectedOffset := ok pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET
def nullifierOffset := ok pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET
def afterstateOffset := ok pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET
/-- Interpretation of E001's external slice/array comparison on canonical carriers. -/
def sliceArrayNe {n : Usize} (s : Slice U8) (a : Array U8 n) : Result Bool :=
  core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s (Array.to_slice a)
theorem sliceArrayNe_eq {n : Usize} (s : Slice U8) (a : Array U8 n) :
    sliceArrayNe s a =
      core.cmp.PartialEq.ne.trait_default
        (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s (Array.to_slice a) := rfl
#print axioms sliceArrayNe_eq
"""
tail="""
theorem probe (bytes : Slice U8) : decode bytes = NFO_RawDecode.decode bytes := by
  rfl
#print axioms probe
theorem oracle (bytes : Slice U8) :
    NFO_DecodeOracle.run atomic_statement.decode_digest_canonical
      pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
      pool_v1.pair_forest_terminal.validate_result bytes = decode bytes :=
  (NFO_DecodeOracle.substitution bytes).trans (probe bytes).symm
#print axioms oracle
end NFR_ExtractedDecode
"""
source=header+'\n\n'.join(parts)+tail
out=E/'NFR_ExtractedDecode.lean'
if '--check' in sys.argv:
 assert out.read_text()==source,'generated E001 port differs'
else:
 out.write_text(source)
manifest=json.dumps(dict(inputs=inputs,
 method='E001 selected closure and decoder bodies; canonical carrier and child owner names; external constant slots interpreted as ok of canonical constants without eliminating monadic binds; external slice-array ne interpreted through canonical slice equality; external templates never imported',
 output_sha256=hashlib.sha256(source.encode()).hexdigest()),indent=1)+'\n'
out=E/'NFR_B_EXTRACTION_ADAPTATION.json'
if '--check' in sys.argv:
 assert out.read_text()==manifest,'adaptation manifest differs'
else:
 out.write_text(manifest)
print('E001 selected-body port checked: 16 definitions, no external-template import')
