from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
def numeric(j):
 if j==0:return 'JHl_Weight00','source'
 if j<3:return 'JHl_Weight01_02',f'source{j:02}'
 st=3+4*((j-3)//4);return f'JHl_Weight{st:02}_{min(st+3,63):02}',f'source{j:02}'
files={}
for st in range(0,64,4):
 name=f'JHl_WeightBytes{st//4:02}'
 s='import JHl_WeightCell\n'+''.join(f'import {n}\n' for n in sorted(set(numeric(j)[0] for j in range(st,st+4))))+f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std
'''
 for j in range(st,st+4):
  nm,th=numeric(j)
  s+=f'''
theorem cell{j:02} : JHl_WeightCell.Law ⟨{j},by decide⟩ := by
  intro q canonical same
  have numeric := {nm}.{th}
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 {j} at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight{j:02}.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop {712+16*j}).take 16
  rw [JFq_Weight{j:02}.selected]
  exact bytes.trans (by rfl)
#print axioms cell{j:02}
'''
 s+=f'end AspisR1.{name}\nend\n';files[name]=s
for name,s in files.items():
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
print('16 four-cell byte modules validated')
