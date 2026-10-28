from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');p=L/'PV_B2_C_TableRange.lean'
extra='theorem member_bound (x : U16) (hx : x ∈ values) : x.val < 1024 := by\n  have h : decide (x.val < 1024) = true := (List.all_eq_true.mp values_range) x hx\n  exact of_decide_eq_true h\n\n/-- Valid reads return a bounded row without reducing the full table. -/\ntheorem read_range (j : Usize) (hj : j.val < (1024#usize).val) :\n    ∃ x : U16, Array.index_usize table j = Result.ok x ∧ x.val < 1024 := by\n  obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec table j (by\n    change j.val < table.val.length\n    simpa only [table.property] using hj))\n  have hm : x ∈ table.val := by\n    rw [hv]\n    exact List.getElem_mem _\n  exact ⟨x,hx,member_bound x hm⟩\n\n#print axioms member_bound\n#print axioms read_range\n'
s='import R1Z.PV_B2_C_Table\nset_option autoImplicit false\nnamespace PV_B2_C_TableRange\nopen Aeneas Aeneas.Std PV_B2_C_Table\n'
for i in range(32):
 s+=f'theorem chunk{i}_range : chunk{i}.all (fun x => decide (x.val < 1024)) = true := by decide\n#print axioms chunk{i}_range\n'
s+='''
/-- A symbolic composition over named 32-entry proofs, no large-type enumeration. -/
theorem values_range : values.all (fun x => decide (x.val < 1024)) = true := by
  simp only [values,List.all_append,'''+','.join(f'chunk{i}_range' for i in range(32))+''',Bool.and_self]

#print axioms values_range
end PV_B2_C_TableRange
'''
s=s.replace('#print axioms values_range',extra+'#print axioms values_range')
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
