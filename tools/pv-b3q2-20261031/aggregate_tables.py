from pathlib import Path
import os
O=Path(os.environ.get('PV_B3Q_OUTPUT','evidence/pv-b3q2-20261031'))/'lean'
s=''.join(f'import PV_B3Q_LinkTable{i}\n'for i in range(9))+'import PV_B3Q_PatternTable\nnamespace PV_B3Q_FrozenTables\n'
s+='def links : List Link := '+ ' ++ '.join(f'links{i}' for i in range(9))+'\n'
s+='theorem links_safe : links.all linkSafe = true := by\n simp only [links,List.all_append,'+','.join(f'links{i}_safe'for i in range(9))+',Bool.true_and]\n'
s+='theorem link_member_safe (l : Link) (member : l ∈ links) :\n    l.1 < 5 ∧ l.2.1 < 64 ∧ l.2.2.1.1 < 1024 ∧ l.2.2.1.2.1 < 2 ∧ l.2.2.1.2.2 < 14 ∧ l.2.2.2.1 < 1024 ∧ l.2.2.2.2.1 < 2 ∧ l.2.2.2.2.2 < 14 := by\n have h := List.all_eq_true.mp links_safe l member\n simpa [linkSafe,endpointSafe,Bool.and_eq_true,and_assoc] using h\n'
s+='def columns : List Nat := '+ ' ++ '.join(f'columns{i}'for i in range(14))+'\n'
s+='theorem columns_safe : columns.all (fun n => decide (n < 16)) = true := by\n simp only [columns,List.all_append,'+','.join(f'columns{i}_safe'for i in range(14))+',Bool.true_and]\n'
s+='theorem column_member_bound (column : Nat) (member : column ∈ columns) : column < 16 := by\n have h := List.all_eq_true.mp columns_safe column member\n exact of_decide_eq_true h\n'
s+='def masks : List Nat := '+ ' ++ '.join(f'masks{i}'for i in range(4))+'\n'
s+='theorem masks_safe : masks.all maskSafe = true := by\n simp only [masks,List.all_append,'+','.join(f'masks{i}_safe'for i in range(4))+',Bool.true_and]\n'
s+='theorem mask_member_cases (mask : Nat) (member : mask ∈ masks) : mask = 6144 ∨ mask = 6145 ∨ mask = 4097 ∨ mask = 2048 ∨ mask = 2049 ∨ mask = 26214 ∨ mask = 1749 := by\n have h := List.all_eq_true.mp masks_safe mask member\n exact of_decide_eq_true h\n'
for n in ['links_safe','link_member_safe','columns_safe','column_member_bound','masks_safe','mask_member_cases']:s+=f'#print axioms {n}\n'
s+='end PV_B3Q_FrozenTables\n'
(O/'PV_B3Q_TableGuards.lean').write_text(s)
