import CuSavingsCanonicalDotsAll
import CuSavingsCanonicalDotsField
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsChecked
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotsField
abbrev Q := Array U32 4#usize

def CanonicalArray (x : Q) : Prop := ∀ value∈x.val,value.val<2147483647

theorem new_constructor (x : Q) (hc : CanonicalArray x) :
    new_pairing.canonical.Q.from_limbs x=.ok (some x) := by
  let inst := new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
  have hcall : ∀ value∈x.to_slice.val,inst.call_mut () value=.ok (true,()) := by
    intro value hv
    have hc := hc value hv
    have hcmp : value<new_pairing.canonical.P := by
      rw [UScalar.lt_equiv]
      simp only [new_pairing.canonical.P,old_pairing.canonical.P]
      change value.val<2147483647
      exact hc
    simp only [inst,new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,hcmp]
    rfl
  have ha := CuSavingsCanonicalDotsAll.source_true inst x.to_slice hcall
    x.to_slice.val.length 0 (Nat.zero_le _) (Nat.sub_zero _)
  simp only [new_pairing.canonical.Q.from_limbs,core.slice.Slice.iter,lift,bind_tc_ok]
  change (do let (b,_) ← AspisR1CanonicalStd.all_loop inst ⟨x.to_slice,0⟩ ()
             if b then .ok (some x) else .ok none) = _
  rw [ha]
  rfl

theorem old_constructor (x : Q) (hc : CanonicalArray x) :
    old_pairing.canonical.Q.from_limbs x=.ok (some x) := by
  let inst := old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
  have hcall : ∀ value∈x.to_slice.val,inst.call_mut () value=.ok (true,()) := by
    intro value hv
    have hc := hc value hv
    have hcmp : value<old_pairing.canonical.P := by
      rw [UScalar.lt_equiv]
      simp only [new_pairing.canonical.P,old_pairing.canonical.P]
      change value.val<2147483647
      exact hc
    simp only [inst,old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,hcmp]
    rfl
  have ha := CuSavingsCanonicalDotsAll.source_true inst x.to_slice hcall
    x.to_slice.val.length 0 (Nat.zero_le _) (Nat.sub_zero _)
  simp only [old_pairing.canonical.Q.from_limbs,core.slice.Slice.iter,lift,bind_tc_ok]
  change (do let (b,_) ← AspisR1CanonicalStd.all_loop inst ⟨x.to_slice,0⟩ ()
             if b then .ok (some x) else .ok none) = _
  rw [ha]
  rfl


def limbs (x : field.QM31) : Q :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]

theorem limbs_canonical (x : field.QM31) (hc : Canonical x) : CanonicalArray (limbs x) := by
  rcases hc with ⟨ha,hb,hc,hd⟩
  intro value hv
  simp only [limbs,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl <;> assumption

theorem checked_q (x : field.QM31) (hc : Canonical x) :
    old_pairing.checked_q x=.ok (.Ok (limbs x)) := by
  have hlimb : old_pairing.limbs_of x=.ok (limbs x) := rfl
  simp only [old_pairing.checked_q,hlimb,bind_tc_ok,
    old_constructor _ (limbs_canonical x hc),core.option.Option.ok_or,AspisR1CanonicalStd.ok_or]

#print axioms new_constructor
#print axioms old_constructor
#print axioms limbs_canonical
#print axioms checked_q
end AspisR1.CuSavingsCanonicalDotsChecked
