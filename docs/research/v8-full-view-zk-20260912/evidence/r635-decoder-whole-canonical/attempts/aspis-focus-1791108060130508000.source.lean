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
  have hoffle : off ≤ xs.length := by omega
  have hwordslen : (blockWords v).length = 8 := by simp [blockWords]
  have hprefixlen : (xs.take off ++ blockWords v).length = off + 8 := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left hoffle]
    rw [hwordslen]
  have hleft : (blockOutput8 block v out).val.length = xs.length := by
    simp [blockOutput8, setNat, xs]
  have hright :
      (xs.take off ++ blockWords v ++ xs.drop fin).length = xs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [hwordslen, hxs, hfin]
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
    have hleftGet : (blockOutput8 block v out).val[i] = xs[i] := by
      simp [blockOutput8, setNat, off, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7]
      rfl
    have hrightGet : (xs.take off ++ blockWords v ++ xs.drop fin)[i] = xs[i] := by
      have htake : i < (xs.take off).length := by
        simpa [List.length_take, Nat.min_eq_left hoffle] using hbefore
      have hpref : i < (xs.take off ++ blockWords v).length := by
        rw [hprefixlen]
        omega
      rw [List.getElem_append_left hpref]
      rw [List.getElem_append_left htake]
      rw [List.getElem_take]
      rfl
    exact hleftGet.trans hrightGet.symm
  · by_cases hafter : fin ≤ i
    · have hn0 : off ≠ i := by omega
      have hn1 : off + 1 ≠ i := by omega
      have hn2 : off + 2 ≠ i := by omega
      have hn3 : off + 3 ≠ i := by omega
      have hn4 : off + 4 ≠ i := by omega
      have hn5 : off + 5 ≠ i := by omega
      have hn6 : off + 6 ≠ i := by omega
      have hn7 : off + 7 ≠ i := by omega
      have hleftGet : (blockOutput8 block v out).val[i] = xs[i] := by
        simp [blockOutput8, setNat, off, fin, hfin, hn0, hn1, hn2, hn3,
          hn4, hn5, hn6, hn7]
      have hrightGet : (xs.take off ++ blockWords v ++ xs.drop fin)[i] = xs[i] := by
        rw [List.getElem_append_right (by rw [hprefixlen, hfin]; omega)]
        rw [List.getElem_drop]
        congr 1
        omega
      exact hleftGet.trans hrightGet.symm
    · have hmid0 : off ≤ i := by omega
      have hmid1 : i < off + 8 := by rw [← hfin]; exact Nat.lt_of_not_ge hafter
      let j := i - off
      have hj0 : j < 8 := by dsimp [j]; omega
      have hij : i = off + j := by dsimp [j]; omega
      have hleftGet : (blockOutput8 block v out).val[i] =
          sourceMaskedValue (sourceWordNat v j (by omega)) := by
        interval_cases j <;> simp [blockOutput8, setNat, off, fin, hfin,
          hij, List.getElem_set]
      have hrightGet : (xs.take off ++ blockWords v ++ xs.drop fin)[i] =
          sourceMaskedValue (sourceWordNat v j (by omega)) := by
        rw [List.getElem_append_left (by rw [hprefixlen]; omega)]
        have htake : (xs.take off).length ≤ i := by
          simp only [List.length_take, Nat.min_eq_left hoffle]
          exact hmid0
        rw [List.getElem_append_right htake]
        have hji : i - (xs.take off).length = j := by
          simp only [List.length_take, Nat.min_eq_left hoffle]
          dsimp [j]
          omega
        rw [hji]
        rw [List.getElem_append_left (by rw [hwordslen]; omega)]
        interval_cases j <;> simp [blockWords, hij, off]
      exact hleftGet.trans hrightGet.symm

#print axioms blockOutput8_segment

end AspisV8R19.R632DecoderBlockArray
