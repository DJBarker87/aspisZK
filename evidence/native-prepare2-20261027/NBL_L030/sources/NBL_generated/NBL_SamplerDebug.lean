import NBL_SamplerNative
import NBL_SecondCarry
set_option autoImplicit false
namespace AspisR1.NBL_SamplerDebug
open Aeneas Aeneas.Std Result
open ExtractedIndexedAddSmallNatModelV1 NBL_SamplerReplay
open SamplerAddDigits

/-- Native gamma's wrapped_again debug assertion follows from the SAME low
and two carry traces. It is not assumed by the second-add replacement. -/
theorem source (block : Bytes32) (d q d1 d2 : Words) (n c1 c2 : U32)
    (tr : LowTrace block d q) (nv : n.val=(quotient q).val+1)
    (first : NBA_AddCarry.Trace (values d) n.val (values d1) c1.val) (nonzero : c1≠0#u32)
    (second : NBA_AddCarry.Trace (values d1) 1 (values d2) c2.val) : c2=0#u32 := by
  have lowResult := low block d q tr
  have bound : n.val≤257 := by have := lowResult.2.2;omega
  have canonical : ∀ x∈values d,x<2147483647 := by
    intro x member
    obtain ⟨word,mem,rfl⟩ := List.mem_map.mp member
    obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp mem
    have i8 : i<8 := by have := d.property;change d.val.length=8 at this;omega
    subst word
    exact lowResult.2.1 i i8
  have size : (values d).length=8 := by
    rw [values,List.length_map]
    exact d.property
  have power : 2147483647≤2147483647^8 := by
    calc
      2147483647=2147483647^1 := by simp
      _≤2147483647^8 := Nat.pow_le_pow_right (by decide) (by decide)
  have small : n.val<2147483647^(values d).length := by rw [size];omega
  have positive : 0<c1.val := by
    by_contra h
    exact nonzero (UScalar.eq_of_val_eq (by omega))
  have firstValue := NBA_AddCarry.source first
  have secondValue := NBA_AddCarry.source second
  have zero := NBL_SecondCarry.natural (by decide : 0<2147483647) (values d) canonical small
    (by rw [firstValue];exact positive)
  rw [firstValue] at zero
  have last := congrArg Prod.snd secondValue
  apply UScalar.eq_of_val_eq
  change c2.val=0
  exact last.symm.trans zero

#print axioms source
end AspisR1.NBL_SamplerDebug
