"""Body-only canonical-carrier adaptation of the pinned emitted decoder.
No axioms, external templates, duplicate carrier owners or generated settings.
"""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;D=E/'NFO_E001_outputs'
root='aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_result_v1'
parts=[];pins=[]
for name in ['Types','Funs']:
 p=D/f'NFO_decode_extracted__NFO_DecodeExtracted__{name}.lean.txt';s=p.read_text();decls=[]
 for m in re.finditer(r'(?m)^def(?:\s|\n)',s):
  end=s.find('\n/--',m.start());end=len(s) if end<0 else end
  block=s[m.start():end].split('\nend NFO_DecodeExtracted')[0].strip()
  # Select only the five closure carriers/functions and top decoder, not
  # definitions whose bodies merely call it.
  head=block.split(':=',1)[0]
  if not re.match(r'def\s+'+re.escape(root)+r'(?:\s|\.)',head):continue
  block=block.replace(root,'decode').replace('aspis_statement.','AspisR1TerminalDecoder.')
  block=block.replace('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES','792#usize')
  block=re.sub(r'(let [a-zA-Z0-9_]+) ←(\s+(?:AspisR1TerminalDecoder\.pool_v1\.[\w.]+(?:MAGIC|VERSION|OFFSET)|792#usize))',r'\1 :=\2',block)
  block=block.replace('Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 s a','core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s (Array.to_slice a)')
  parts.append(block);decls.append(block.split(':=',1)[0].strip())
 pins.append(dict(input=str(p.relative_to(E)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declarations=decls))
assert len(parts)==16,len(parts)
source='''import JHb_Emit
set_option autoImplicit false
noncomputable section
namespace NFO_RawDecode
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
'''+ '\n\n'.join(parts)+'''\n#print axioms decode
end NFO_RawDecode
'''
assert not re.search(r'\b(?:axiom|sorry|admit|native_decide)\b',source)
(E/'NFO_RawDecode.lean').write_text(source)
(E/'NFO_DECODE_ADAPTATION.json').write_text(json.dumps(dict(method='body-only substitution: current result decoder name -> NFO_RawDecode.decode; aspis_statement prefix -> canonical AspisR1TerminalDecoder; imported pure child owners retained; Rust constexpr Result slots use canonical pure constants, result width792; U8 slice/array comparison uses the existing slice comparison after Array.to_slice. This is a candidate source association, not a proved roundtrip.',inputs=pins,output_sha256=hashlib.sha256(source.encode()).hexdigest()),indent=1)+'\n')
print('Adapted',len(parts),'definitions to existing cohort carriers')
