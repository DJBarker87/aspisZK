import PV_B3Q_LinkTable0
import PV_B3Q_LinkTable1
import PV_B3Q_LinkTable2
import PV_B3Q_LinkTable3
import PV_B3Q_LinkTable4
import PV_B3Q_LinkTable5
import PV_B3Q_LinkTable6
import PV_B3Q_LinkTable7
import PV_B3Q_LinkTable8
import PV_B3Q_PatternTable
namespace PV_B3Q_FrozenTables
def links : List Link := links0 ++ links1 ++ links2 ++ links3 ++ links4 ++ links5 ++ links6 ++ links7 ++ links8
theorem links_safe : links.all linkSafe = true := by
 simp only [links,List.all_append,links0_safe,links1_safe,links2_safe,links3_safe,links4_safe,links5_safe,links6_safe,links7_safe,links8_safe,Bool.true_and]
theorem link_member_safe (l : Link) (member : l ∈ links) :
    l.1 < 5 ∧ l.2.1 < 64 ∧ l.2.2.1.1 < 1024 ∧ l.2.2.1.2.1 < 2 ∧ l.2.2.1.2.2 < 14 ∧ l.2.2.2.1 < 1024 ∧ l.2.2.2.2.1 < 2 ∧ l.2.2.2.2.2 < 14 := by
 have h := List.all_eq_true.mp links_safe l member
 simpa [linkSafe,endpointSafe,Bool.and_eq_true,and_assoc] using h
def columns : List Nat := columns0 ++ columns1 ++ columns2 ++ columns3 ++ columns4 ++ columns5 ++ columns6 ++ columns7 ++ columns8 ++ columns9 ++ columns10 ++ columns11 ++ columns12 ++ columns13
theorem columns_safe : columns.all (fun n => decide (n < 16)) = true := by
 simp only [columns,List.all_append,columns0_safe,columns1_safe,columns2_safe,columns3_safe,columns4_safe,columns5_safe,columns6_safe,columns7_safe,columns8_safe,columns9_safe,columns10_safe,columns11_safe,columns12_safe,columns13_safe,Bool.true_and]
theorem column_member_bound (column : Nat) (member : column ∈ columns) : column < 16 := by
 have h := List.all_eq_true.mp columns_safe column member
 exact of_decide_eq_true h
def masks : List Nat := masks0 ++ masks1 ++ masks2 ++ masks3
theorem masks_safe : masks.all maskSafe = true := by
 simp only [masks,List.all_append,masks0_safe,masks1_safe,masks2_safe,masks3_safe,Bool.true_and]
theorem mask_member_cases (mask : Nat) (member : mask ∈ masks) : mask = 6144 ∨ mask = 6145 ∨ mask = 4097 ∨ mask = 2048 ∨ mask = 2049 ∨ mask = 26214 ∨ mask = 1749 := by
 have h := List.all_eq_true.mp masks_safe mask member
 exact of_decide_eq_true h
#print axioms links_safe
#print axioms link_member_safe
#print axioms columns_safe
#print axioms column_member_bound
#print axioms masks_safe
#print axioms mask_member_cases
end PV_B3Q_FrozenTables
