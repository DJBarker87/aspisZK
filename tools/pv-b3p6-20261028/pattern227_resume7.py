"""Generate finite column-bound facts for literal14x16 pattern table."""
from pathlib import Path
import re,sys
L=Path('evidence/pv-b3p6-20261028/lean');s=(L/'PV_B3P_E227_06.lean').read_text()
cols=[]
for i in range(14):
 b=s.split('constants.pattern_'+str(i)+' :',1)[1].split('\nprivate def',1)[0]
 text=b.split('columns :=',1)[1].split('offsets :=',1)[0]
 nums=re.findall(r'(\d+)#u8',text)
 if not nums:
  assert 'pattern_let_a7'in text
  nums=['0']*16
 assert len(nums)==16,(i,nums);cols.append(nums)
out=['import PV_B3P_Success227','import PV_B3P_E227_15','namespace PV_B3P_Success227','open Aeneas Aeneas.Std PV_B3P_227','set_option autoImplicit false','',
'''def PatternSafe (p : reference_copy_terminal.CompiledPoolV1PairForestPattern) : Prop :=
  ∀ c ∈ p.columns.val, c.val<16

theorem patterns_safe (p : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (hp : p ∈ reference_copy_terminal.constants.COPY_PATTERNS.val) : PatternSafe p := by
  unfold reference_copy_terminal.constants.COPY_PATTERNS at hp
  simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with '''+' | '.join(['rfl']*14)]
for ns in cols:
 out+=['  · intro c hc','    change c ∈ ['+', '.join(n+'#u8'for n in ns)+'] at hc','    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc','    rcases hc with '+' | '.join(['rfl']*16)+' <;> scalar_tac']
out+=['','#print axioms patterns_safe','end PV_B3P_Success227','']
data='\n'.join(out);p=L/'PV_B3P_PatternBounds227.lean'
if '--check'in sys.argv:assert p.read_text()==data
else:p.write_text(data)
