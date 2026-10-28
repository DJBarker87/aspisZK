from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent;R=D.parents[1];data=json.loads((D/'JHk_LINE_PREFLIGHT.json').read_text());rows=data['rows'];assert data['rhs_matches']
def lit(a):
 if len(a)==2:return '⟨'+','.join(map(str,a))+'⟩'
 return '⟨'+lit(a[:len(a)//2])+','+lit(a[len(a)//2:])+'⟩'
for i,row in enumerate(rows):
 before_rhs=(0,)*8 if i==0 else tuple(rows[i-1]['rhs']);before_power=(1,0,0,0) if i==0 else tuple(rows[i-1]['power'])
 before_r='(0 : FE)' if i==0 else f'JHk_Rhs{i-1:02}.rhs'
 before_p='(1 : K)' if i==0 else f'JHk_Rhs{i-1:02}.power'
 imports=f'import JHk_Line{i:02}\nimport JFq_Rho\nimport JFq_Rhs\n'+('' if i==0 else f'import JHk_Rhs{i-1:02}\n')
 text=imports+f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs{i:02}
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := {lit(row['rhs'])}
def power : K := {lit(row['power'])}
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : {before_r}+LiteralOpeningView.eK {before_p}*JHk_Line{i:02}.value=rhs := by
'''
 if i==0:text+='  rw [map_one,one_mul,zero_add]\n  rfl\n'
 else:text+=f'''  change ({lit(before_rhs)} : FE)+{lit(before_power+(0,)*4)}*{lit(row['value'])}={lit(row['rhs'])}
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
'''
 text+='#print axioms rhs_step\n'
 text+=f'theorem power_step : {before_p}*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by\n'
 if i==0:text+='  rw [one_mul]\n  rfl\n'
 else:text+=f'''  change ({lit(before_power)} : K)*{lit(rows[0]['power'])}={lit(row['power'])}
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
'''
 text+='#print axioms power_step\n'
 if i==9:text+='theorem retained : rhs=CheckpointBytes5Output.ofE JFq_Rhs.scalar := rfl\n#print axioms retained\n'
 text+=f'end AspisR1.JHk_Rhs{i:02}\nend\n'
 p=R/f'lean/JHk_Rhs{i:02}.lean'
 if '--check' in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
print('Validated ten bounded rhs/power cells; first zero/one cell uses symbolic identities.')
