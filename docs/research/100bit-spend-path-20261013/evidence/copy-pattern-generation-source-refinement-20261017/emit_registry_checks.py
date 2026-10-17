from pathlib import Path
import hashlib,json,sys,argparse
parser=argparse.ArgumentParser()
parser.add_argument("--output",type=Path,default=Path("/tmp"))
parser.add_argument("--check",action="store_true")
args=parser.parse_args()
rows={'A':list(range(6)),'B':[6,7,8,9,11,12,13]}
outputs={}
for label,indices in rows.items():
 text='''import AspisR1.CopyPatternRegistryModel10

/-! Small descriptor-data checks. The exceptional offset record is proved first
in CopyPatternRegistryModel10. No field expression is normalized. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternRegistryModel
noncomputable section
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact

'''
 for i in indices:
  text+=f'''theorem raw{i}_columns : ∀ j : Fin 16, (cell (rawAt {i}).columns j).val < 16 := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw{i}_offsets : ∀ j : Fin 16,
    (cell (rawAt {i}).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell
  intro j
  fin_cases j <;> decide

theorem raw{i}_model : modelPattern (rawAt {i}) raw{i}_columns = R0P.copyPattern{i} := by
  unfold modelPattern R0P.copyPattern{i}
  congr 1
  all_goals
    funext j
    fin_cases j <;> (unfold rawAt Registry AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS cell; rfl)

#print axioms raw{i}_columns
#print axioms raw{i}_offsets
#print axioms raw{i}_model

'''
 text+='end\nend AspisR1.CopyPatternRegistryModel\n'
 outputs[f'CopyPatternRegistryModel{label}.lean']=text
check=args.check
for name,text in outputs.items():
 p=args.output/name
 if check: assert p.read_text()==text,name
 else:p.write_text(text)
 print(name,hashlib.sha256(text.encode()).hexdigest())
