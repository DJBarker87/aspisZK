import NEA_TableA00
import NEA_TableA01
import NEA_TableA02
import NEA_TableA03
import NEA_TableA04
import NEA_TableA05
import NEA_TableA06
import NEA_TableA07
import NEA_TableA08
import NEA_TableA09
import NEA_TableA10
import NEA_TableA11
import NEA_TableA12
import NEA_TableA13
import NEA_TableA14
import NEA_TableA15
import NEA_TableB00
import NEA_TableB01
import NEA_TableB02
import NEA_TableB03
import NEA_TableB04
import NEA_TableB05
import NEA_TableB06
import NEA_TableB07
import NEA_TableB08
import NEA_TableB09
import NEA_TableB10
import NEA_TableB11
import NEA_TableB12
import NEA_TableB13
import NEA_TableB14
import NEA_TableB15
import R17ActualTableArrayIndexV1
set_option autoImplicit false
namespace NEA_TableCanonical
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

theorem entriesA (p : U32 × U32) (member : p ∈ fast_domain.TABLE_A_entries) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  simp only [fast_domain.TABLE_A_entries,List.append_assoc,List.mem_append] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact NEA_TableA00.canonical p h0
  · exact NEA_TableA01.canonical p h1
  · exact NEA_TableA02.canonical p h2
  · exact NEA_TableA03.canonical p h3
  · exact NEA_TableA04.canonical p h4
  · exact NEA_TableA05.canonical p h5
  · exact NEA_TableA06.canonical p h6
  · exact NEA_TableA07.canonical p h7
  · exact NEA_TableA08.canonical p h8
  · exact NEA_TableA09.canonical p h9
  · exact NEA_TableA10.canonical p h10
  · exact NEA_TableA11.canonical p h11
  · exact NEA_TableA12.canonical p h12
  · exact NEA_TableA13.canonical p h13
  · exact NEA_TableA14.canonical p h14
  · exact NEA_TableA15.canonical p h15

theorem readA (i : Usize) (bound : i.val < 512) (p : U32 × U32)
    (read : Array.index_usize fast_domain.TABLE_A i=ok p) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  have same := Result.ok.inj (read.symm.trans
    (R17ActualTableArrayIndexV1.tableA_index_entries i bound))
  rw [same]
  exact entriesA _ (List.getElem_mem _)
#print axioms entriesA
#print axioms readA

theorem entriesB (p : U32 × U32) (member : p ∈ fast_domain.TABLE_B_entries) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  simp only [fast_domain.TABLE_B_entries,List.append_assoc,List.mem_append] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact NEA_TableB00.canonical p h0
  · exact NEA_TableB01.canonical p h1
  · exact NEA_TableB02.canonical p h2
  · exact NEA_TableB03.canonical p h3
  · exact NEA_TableB04.canonical p h4
  · exact NEA_TableB05.canonical p h5
  · exact NEA_TableB06.canonical p h6
  · exact NEA_TableB07.canonical p h7
  · exact NEA_TableB08.canonical p h8
  · exact NEA_TableB09.canonical p h9
  · exact NEA_TableB10.canonical p h10
  · exact NEA_TableB11.canonical p h11
  · exact NEA_TableB12.canonical p h12
  · exact NEA_TableB13.canonical p h13
  · exact NEA_TableB14.canonical p h14
  · exact NEA_TableB15.canonical p h15

theorem readB (i : Usize) (bound : i.val < 512) (p : U32 × U32)
    (read : Array.index_usize fast_domain.TABLE_B i=ok p) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  have same := Result.ok.inj (read.symm.trans
    (R17ActualTableArrayIndexV1.tableB_index_entries i bound))
  rw [same]
  exact entriesB _ (List.getElem_mem _)
#print axioms entriesB
#print axioms readB
end NEA_TableCanonical
