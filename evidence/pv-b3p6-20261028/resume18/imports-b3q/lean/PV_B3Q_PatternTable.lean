import PV_B3Q_TableTypes
namespace PV_B3Q_FrozenTables
def columns0 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
theorem columns0_safe : columns0.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns0_safe
def columns1 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns1_safe : columns1.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns1_safe
def columns2 : List Nat := [2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns2_safe : columns2.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns2_safe
def columns3 : List Nat := [0, 1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns3_safe : columns3.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns3_safe
def columns4 : List Nat := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns4_safe : columns4.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns4_safe
def columns5 : List Nat := [6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns5_safe : columns5.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns5_safe
def columns6 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns6_safe : columns6.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns6_safe
def columns7 : List Nat := [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns7_safe : columns7.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns7_safe
def columns8 : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns8_safe : columns8.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns8_safe
def columns9 : List Nat := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns9_safe : columns9.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns9_safe
def columns10 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns10_safe : columns10.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns10_safe
def columns11 : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns11_safe : columns11.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns11_safe
def columns12 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns12_safe : columns12.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns12_safe
def columns13 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0]
theorem columns13_safe : columns13.all (fun n => decide (n < 16)) = true := by decide
#print axioms columns13_safe
def masks0 : List Nat := [6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145]
theorem masks0_safe : masks0.all maskSafe = true := by decide
#print axioms masks0_safe
def masks1 : List Nat := [6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145]
theorem masks1_safe : masks1.all maskSafe = true := by decide
#print axioms masks1_safe
def masks2 : List Nat := [2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145]
theorem masks2_safe : masks2.all maskSafe = true := by decide
#print axioms masks2_safe
def masks3 : List Nat := [6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214, 26214, 26214, 26214, 1749]
theorem masks3_safe : masks3.all maskSafe = true := by decide
#print axioms masks3_safe
end PV_B3Q_FrozenTables
