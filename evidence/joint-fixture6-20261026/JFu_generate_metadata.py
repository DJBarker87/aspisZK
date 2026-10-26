from pathlib import Path
import re,sys,json
R=Path(__file__).resolve().parents[2];b=[]
for line in (R/'lean/JFx_DataPublic00.lean').read_text().splitlines():
 if line.startswith('def c'):
  if 'List.replicate' in line:
   n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',line).groups());b.extend([v]*n)
  else:b.extend(map(int,re.findall(r'(\d+)#u8',line)))
windows=[(144,32),(176,48),(224,32),(256,32),(288,8),(296,8),(976,16),(1664,8),(1812,4)]
lens=','.join(f'JFx_DataPublic00.c{i:02}_length' for i in range(59))
rules='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
for i,(off,n) in enumerate(windows):
 m=f'JFu_PublicMeta{i:02}';data=b[off:off+n];lit='['+','.join(f'{v}#u8' for v in data)+']'
 s=f'''import JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.{m}
open Aeneas Aeneas.Std Result

def bytes : List U8 := {lit}
theorem length : bytes.length={n} := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (JFx_NativeBytes.publicInput.val.drop {off}).take {n}=bytes := by
  change (JFx_DataPublic00.bytes.drop {off}).take {n}=bytes
  simp only [JFx_DataPublic00.bytes,{lens},{rules}]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.publicInput {{start:={off}#usize,«end»:={off+n}#usize}}=
    ok (JFu_PublicRange.segment {off} {n} (by decide)) :=
  by
    have call:=JFu_PublicRange.read {off}#usize {off+n}#usize (by decide) (by decide)
    simpa only [show ({off}#usize).val={off} from rfl,
      show ({off+n}#usize).val={off+n} from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.{m}
'''
 p=R/'lean'/f'{m}.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print(json.dumps({'windows':windows,'check':'--check' in sys.argv}))
