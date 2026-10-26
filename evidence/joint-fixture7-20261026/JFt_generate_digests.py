from pathlib import Path
import re,sys,json
root=Path(__file__).resolve().parents[2]
records=[]
for i in range(47):
 old=f'JFu_PublicDigest{i:02}'
 s=(root/'lean'/f'{old}.lean').read_text()
 nums=[int(x) for x in re.search(r'def bytes : List U8 := \[(.*?)\]',s).group(1).replace('#u8','').split(',')]
 off=int(re.search(r'publicInput.val.drop (\d+)',s).group(1))
 vals=[int.from_bytes(bytes(nums[j:j+4]),'little') for j in range(0,32,4)]
 mod=f'JFt_Digest{i:02}'
 body=f'''import {old}
import JFt_DigestInjective
import JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [{','.join(str(x)+'#u32' for x in vals)}]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest {old}.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=JFu_DigestSliceFacts.source {old}.window
    {old}.length {old}.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value={old}.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,{old}.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : JFu_PublicRange.segment {off} 32 (by decide)={old}.window := by
  apply Subtype.ext
  exact {old}.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment {off} 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.{mod}
'''
 if i>=7:
  body=body.replace('  exact '+old+'.selected','  dsimp only [JFu_PublicRange.segment,'+old+'.window]\n  exact '+old+'.selected')
 path=root/'lean'/f'{mod}.lean'
 if '--check' in sys.argv:assert path.read_text()==body
 else:path.write_text(body)
 records.append(dict(module=mod,offset=off,values=vals))
print(json.dumps(dict(check='--check' in sys.argv,cells=records),indent=2))
