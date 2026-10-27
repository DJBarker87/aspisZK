import XRk_ResultTools
open Aeneas Aeneas.Std Result
namespace XRk_PowersArray
open XRk_ResultTools
#print Array.set

theorem write_prefix {T : Type} {N : Usize} (a : Array T N) (i : Usize)
    (old : T) (back : T → Array T N) (h : Array.index_mut_usize a i = ok (old,back))
    (hi : i.val < a.val.length) (p : T) :
    (back p).val.take (i.val+1) = a.val.take i.val ++ [p] := by
  unfold Array.index_mut_usize at h
  obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  have same := congrArg Prod.snd (Result.ok.inj h)
  change a.set i = back at same
  rw [←same]
  change (a.val.set i.val p).take (i.val+1) = _
  rw [List.take_succ,List.take_set_of_le (Nat.le_refl i.val)]
  simp only [List.getElem?_set_self hi,Option.toList_some]

theorem add_one_value (i N j : Usize) (hi : i.val < N.val)
    (h : i + 1#usize = ok j) : j.val = i.val+1 := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
  have same := Result.ok.inj (hz.symm.trans h)
  simpa only [same] using hval
#print axioms write_prefix
#print axioms add_one_value
end XRk_PowersArray
