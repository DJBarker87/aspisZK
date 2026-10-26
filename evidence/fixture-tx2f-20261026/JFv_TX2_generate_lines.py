from pathlib import Path
import re,sys
P=2147483647
root=Path(__file__).resolve().parents[2]
for i in range(12):
 src=(root/f'lean/JFs_TX2_Geo{10+i}.lean').read_text()
 inputs=re.findall(r'operations (\d+)#usize=ok value[012]',src)
 vals=[int(x) for x in re.findall(r'def value[012].*?⟨(\d+)#u32',src)]
 out=f"import JFv_TX2_LineCall\nimport JFs_TX2_Geo{10+i}\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JFv_TX2_Line{10+i}\nopen Aeneas Aeneas.Std Result\nopen AspisR1QueryGeometryActual\n"
 # query node uses twice squaring, also endpoints
 for k,x in enumerate(vals):
  z=(2*x*x-1)%P
  out+=f"def value{k} : U32 := {z}#u32\n"
  out+=f"theorem source{k} : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations {inputs[k]}#usize=ok value{k} := by\n"
  out+=f"  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo{10+i}.source{k}\n"
  out+=f"  change z.val=(({x}*{x}%2147483647+{x}*{x}%2147483647)%2147483647+2147483647-1)%2147483647 at value\n  norm_num at value\n  have same : z=value{k} := UScalar.eq_of_val_eq value\n  exact same ▸ run\n#print axioms source{k}\n"
 out+=f"end AspisR1.JFv_TX2_Line{10+i}\nend\n"
 target=root/f'lean/JFv_TX2_Line{10+i}.lean'
 if '--check' in sys.argv: assert target.read_text()==out
 else: target.write_text(out)
