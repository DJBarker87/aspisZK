import AspisV8R19.R624DecoderInnerExecution

set_option autoImplicit false
namespace AspisV8R19.R632DecoderBlockArray

open AspisV8R19.R624DecoderInnerExecution
open Aeneas Aeneas.Std

theorem blockOutput8_segment {N : Usize} (block : Usize)
    (v : Array U64 8#usize) (out : Array U32 N)
    (hblock : 8 * (block.val + 1) ≤ N.val) :
    (blockOutput8 block v out).val =
      out.val.take (8 * block.val) ++ blockWords v ++
        out.val.drop (8 * (block.val + 1)) := by
  let xs := out.val
  let off := 8 * block.val
  let fin := 8 * (block.val + 1)
  have hxs : xs.length = N.val := out.property
  have hoff : off + 8 ≤ xs.length := by
    dsimp [off]
    rw [hxs]
    omega
  have hfin : fin = off + 8 := by dsimp [fin, off]; omega
  have hleft : (blockOutput8 block v out).val.length = xs.length := by
    simp [blockOutput8, setNat, xs]
  have hright :
      (xs.take off ++ blockWords v ++ xs.drop fin).length = xs.length := by
    simp only [List.length_append, List.length_take, List.length_drop, blockWords]
    rw [hxs, hfin]
    omega
  apply List.ext_getElem (by rw [hleft, hright])
  intro i hiL hiR
  have hi : i < xs.length := by simpa [blockOutput8, setNat, xs] using hiL
  by_cases hbefore : i < off
  · have hn0 : off ≠ i := by omega
    have hn1 : off + 1 ≠ i := by omega
    have hn2 : off + 2 ≠ i := by omega
    have hn3 : off + 3 ≠ i := by omega
    have hn4 : off + 4 ≠ i := by omega
    have hn5 : off + 5 ≠ i := by omega
    have hn6 : off + 6 ≠ i := by omega
    have hn7 : off + 7 ≠ i := by omega
    simp [blockOutput8, setNat, xs, off, fin, hbefore, hn0, hn1, hn2, hn3,
      hn4, hn5, hn6, hn7, List.getElem_append_left, List.getElem_take]
  · by_cases hafter : fin ≤ i
    · have hn0 : off ≠ i := by omega
      have hn1 : off + 1 ≠ i := by omega
      have hn2 : off + 2 ≠ i := by omega
      have hn3 : off + 3 ≠ i := by omega
      have hn4 : off + 4 ≠ i := by omega
      have hn5 : off + 5 ≠ i := by omega
      have hn6 : off + 6 ≠ i := by omega
      have hn7 : off + 7 ≠ i := by omega
      simp [blockOutput8, setNat, xs, off, fin, hfin, hafter, hn0, hn1,
        hn2, hn3, hn4, hn5, hn6, hn7, List.getElem_append_right,
        List.getElem_drop]
    · have hmid0 : off ≤ i := by omega
      have hmid1 : i < off + 8 := by rw [← hfin]; exact Nat.lt_of_not_ge hafter
      let j := i - off
      have hj0 : j < 8 := by dsimp [j]; omega
      have hij : i = off + j := by dsimp [j]; omega
      interval_cases j <;> simp [blockOutput8, setNat, xs, off, fin, hfin,
        j, hij, List.getElem_append, List.getElem_take, List.getElem_drop]

#print axioms blockOutput8_segment

end AspisV8R19.R632DecoderBlockArray
