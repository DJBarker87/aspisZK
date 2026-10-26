"""Emit named symbolic native decode applications, never concrete digest reduction."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]
s='''import JFs_SerializedDigest
import JFt_PublicValues
import JFt_DigestArray
set_option autoImplicit false
namespace AspisR1.JFs_SerializedDigests
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
'''
for i in range(47):
    k=f'{i:02}'
    src=(R/f'lean/JFu_PublicDigest{k}.lean').read_text()
    off=int(re.search(r'publicInput.val.drop (\d+)',src).group(1))
    s+=f'''
theorem bytes{k} : encodeWords JFt_Digest{k}.value.val=JFu_PublicDigest{k}.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest{k}.bytes,JFu_PublicDigest{k}.length⟩
  have selected : (JFu_PublicRange.segment {off} 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest{k}.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest{k}.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes{k}
'''
s+='end AspisR1.JFs_SerializedDigests\n'
p=R/'lean/JFs_SerializedDigests.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('47 named symbolic digest applications match')
