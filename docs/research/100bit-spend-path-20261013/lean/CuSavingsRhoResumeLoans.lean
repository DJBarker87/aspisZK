import CuSavingsRhoInitRow

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoResumeLoans
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow
abbrev It := core.slice.iter.IterMut field.QM31

def CanonicalFrom (slice : Slice field.QM31) (start : Nat) : Prop :=
  ∀ (j : Nat) (hj : j<slice.val.length),start≤j → Canonical (slice.val[j]'hj)

def BackGood (back : It → It) (start size : Nat) : Prop :=
  ∀ tail : It,tail.slice.val.length=size → CanonicalFrom tail.slice start →
    (back tail).slice.val.length=size ∧ CanonicalFrom (back tail).slice 0

def writeAt (index : Nat) (value : field.QM31) (tail : It) : It :=
  {tail with slice:=tail.slice.setAtNat index value}

theorem back_identity (size : Nat) : BackGood (fun it : It => it) 0 size := by
  intro tail hlen hc
  exact ⟨hlen,hc⟩

theorem back_write (back : It → It) (index size : Nat) (value : field.QM31)
    (hback : BackGood back index size) (hi : index<size) (hc : Canonical value) :
    BackGood (fun tail => back (writeAt index value tail)) (index+1) size := by
  intro tail hlen htail
  apply hback (writeAt index value tail)
  · simpa only [writeAt,Slice.setAtNat,List.length_set] using hlen
  · intro j hj hmin
    have hj0 : j<tail.slice.val.length := by
      simpa only [writeAt,Slice.setAtNat,List.length_set] using hj
    change Canonical ((tail.slice.val.set index value)[j]'_)
    by_cases heq : index=j
    · subst j
      simpa only [List.getElem_set_self] using hc
    · simp only [List.getElem_set,if_neg heq]
      exact htail j hj0 (by omega)

theorem back_done (back : It → It) (iter : It) (size : Nat)
    (hback : BackGood back size size) (hlen : iter.slice.val.length=size) :
    (back iter).slice.val.length=size ∧ CanonicalFrom (back iter).slice 0 := by
  apply hback iter hlen
  intro j hj hmin
  omega

#print axioms back_identity
#print axioms back_write
#print axioms back_done
end AspisR1.CuSavingsRhoResumeLoans
