from pathlib import Path
import re,sys,runpy
P=Path(__file__).resolve().parent;R=P.parents[1]
x=runpy.run_path(str(P/'JGo_arithmetic.py'))
for base in range(0,64,8):
 ns=f'JGo_TX2_Message{base:02}'
 src=(R/f'lean/JGe_Window31_{base:02}.lean').read_text()
 s=f'''import JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
'''
 for i in range(base,base+8):
  raw=re.search(rf'def c{i:02} : List U8 := \[(.*?)\]',src).group(1)
  b=bytes(map(int,re.findall(r'(\d+)#u8',raw)));w=[int.from_bytes(b[k:k+4],'little') for k in range(0,32,4)]
  s+=f'''def bytes{i:02} : Array U8 32#usize := ⟨JGe_Window31.c{i:02},by rfl⟩
def value{i:02} : AspisR1Stage2.Stage2Finish.E := {x['wide'](w)}
def record{i:02} : AspisR1RecordParser.field.wide_exact.WideExact := {x['wide'](w)}
theorem selected{i:02} : ((JFw_Frames.window 8007 2048).val.drop (32*{i})).take 32=bytes{i:02}.val := by
  rw [JGo_TX2_MessageRead.cell {i} (by decide)]
  exact JGe_Window31.selected{i:02}
#print axioms selected{i:02}
theorem parser{i:02} : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes{i:02})=ok (some record{i:02}) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes{i:02} record{i:02}).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser{i:02}
theorem field{i:02} : FIn_Primitives.field (JFw_Frames.window 8007 2048) {i}#usize=ok value{i:02} :=
  JGo_TX2_FieldRead.source _ _ bytes{i:02} record{i:02}
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected{i:02} parser{i:02}
#print axioms field{i:02}
theorem native_parser{i:02} : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes{i:02})=ok (some (FIo_Install.toE value{i:02})) := by
  with_unfolding_all rfl
#print axioms native_parser{i:02}
theorem native_field{i:02} : FIo_Native.weights.field (JFw_Frames.window 8007 2048) {i}#usize=
    ok (FIo_Install.toE value{i:02}) :=
  JGo_TX2_MessageRead.native _ {i}#usize {32*i}#usize {i+1}#usize {32*(i+1)}#usize bytes{i:02} _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value {i}#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value {i}#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value {i+1}#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes{i:02} (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected{i:02}) native_parser{i:02}
#print axioms native_field{i:02}
theorem canonical{i:02} : Port4C_QueryArithmetic.CanonE value{i:02} := by decide
#print axioms canonical{i:02}
'''
 s+=f'end AspisR1.{ns}\nend\n'
 p=R/'lean'/(ns+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('64 message cell outputs in eight modules')
