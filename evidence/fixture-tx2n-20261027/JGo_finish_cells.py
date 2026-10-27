from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]
def generate():
 out={}
 for r in range(2):
  name=29+r; off=[7527,7783][r]
  src=(R/f'lean/JGe_Window{name}_00.lean').read_text()
  for i in range(7):
   j=i+r; tag=f'{r}_{i}'
   raw=re.search(rf'def c{j:02} : List U8 := \[(.*?)\]',src).group(1)
   b=bytes(map(int,re.findall(r'(\d+)#u8',raw)))
   w=[int.from_bytes(b[k:k+4],'little') for k in range(0,32,4)]
   def wide(w):return '⟨⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩,⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩⟩'%tuple(w)
   s=f'''import JGo_TX2_FieldRead
import JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell{tag}
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window{name}.c{j:02},by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := {wide(w)}
def native : AspisR1RecordParser.field.wide_exact.WideExact := {wide(w)}

theorem selected : ((JFw_Frames.window {off} 224).val.drop (32*{i})).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell {off} {i} (by decide)]
  exact JGe_Window{name}.selected{j:02}
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window {off} 224) {i}#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length {off} 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length {off} 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell{tag}
end
'''
   out[f'JGo_TX2_Cell{tag}.lean']=s
 return out
for f,s in generate().items():
 p=R/'lean'/f
 if '--check' in sys.argv:assert p.read_text()==s,f
 else:p.write_text(s)
print('14 final-round cell modules match' if '--check' in sys.argv else 'generated 14 cell modules')
