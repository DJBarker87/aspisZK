from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2]
s=(R/'lean/JFx_DataPublic00.lean').read_text()
b=[]
for line in s.splitlines():
 if not line.startswith('def c'):continue
 if 'List.replicate' in line:
  n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',line).groups());b.extend([v]*n)
 else:b.extend(map(int,re.findall(r'(\d+)#u8',line)))
assert len(b)==1880
windows=[112,304]+list(range(336,976,32))+[992]+list(range(1024,1664,32))+[1744,1776,1816,1848]
assert len(windows)==47
rules='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
lens=','.join(f'JFx_DataPublic00.c{i:02}_length' for i in range(59))
outputs={}
for i,off in enumerate(windows):
 data=b[off:off+32];assert len(data)==32
 assert all(int.from_bytes(bytes(data[j:j+4]),'little')<2147483647 for j in range(0,32,4)),off
 name=f'JFu_PublicDigest{i:02}'
 lit='['+','.join(f'{v}#u8' for v in data)+']'
 s=f'''import JFu_DigestSlice
import JFz_CanonicalAppend
import JFx_NativeBytes
set_option autoImplicit false
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := {lit}
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (JFx_NativeBytes.publicInput.val.drop {off}).take 32=bytes := by
  change (JFx_DataPublic00.bytes.drop {off}).take 32=bytes
  simp only [JFx_DataPublic00.bytes,{lens},{rules}]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical {str(data).replace(' ', '')}
  simp only [canonical_four]
  exact '''+('⟨by norm_num [little], '*8)+'JFz_Canonical.nil'+('⟩'*8)+f'''

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.{name}
'''
 outputs[R/'lean'/f'{name}.lean']=s
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print(json.dumps({'windows':windows,'public_sha256':hashlib.sha256(bytes(b)).hexdigest(),'modules':len(outputs),'check':'--check' in sys.argv}))
