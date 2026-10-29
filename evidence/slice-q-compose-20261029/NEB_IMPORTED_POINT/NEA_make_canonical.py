from pathlib import Path
E=Path(__file__).resolve().parent
s=''.join(f'import NEA_Table{t}{i:02d}\n' for t in 'AB' for i in range(16))
s+='import R17ActualTableArrayIndexV1\nset_option autoImplicit false\nnamespace NEA_TableCanonical\nopen Aeneas Aeneas.Std Result AspisR1QueryGeometryActual\n'
for table in 'AB':
 s+=f'''\ntheorem entries{table} (p : U32 × U32) (member : p ∈ fast_domain.TABLE_{table}_entries) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  simp only [fast_domain.TABLE_{table}_entries,List.append_assoc,List.mem_append] at member
  rcases member with '''+' | '.join(f'h{i}' for i in range(16))+'\n'
 for i in range(16):s+=f'  · exact NEA_Table{table}{i:02d}.canonical p h{i}\n'
 s+=f'''\ntheorem read{table} (i : Usize) (bound : i.val < 512) (p : U32 × U32)
    (read : Array.index_usize fast_domain.TABLE_{table} i=ok p) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  have same := Result.ok.inj (read.symm.trans
    (R17ActualTableArrayIndexV1.table{table}_index_entries i bound))
  rw [same]
  exact entries{table} _ (List.getElem_mem _)
#print axioms entries{table}
#print axioms read{table}
'''
s+='end NEA_TableCanonical\n';(E/'NEA_TableCanonical.lean').write_text(s)
