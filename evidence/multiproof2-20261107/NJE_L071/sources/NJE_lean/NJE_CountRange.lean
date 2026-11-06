import NJE_CountRows

set_option autoImplicit false
namespace NJE_CountRange
open Aeneas Aeneas.Std Result

def successor (s : U32) : U32 := U32.wrapping_add s 1#u32

theorem value (s : U32) (bound : s.val<18) : (successor s).val=s.val+1 := by
 unfold successor U32.wrapping_add UScalar.wrapping_add
 change (s.val+1)%2^32=s.val+1
 exact Nat.mod_eq_of_lt (by omega)

theorem active (s : U32) (bound : s.val<18) :
 core.iter.range.IteratorRange.next core.iter.range.StepU32 {start:=s,«end»:=18#u32}=
   ok (some s,{start:=successor s,«end»:=18#u32}) := by
 have word : s+1#u32=successor s := by apply UScalar.eq_of_val_eq;rw [value s bound];scalar_tac
 simp [core.iter.range.IteratorRange.next,core.iter.range.StepU32,
   core.iter.range.UScalarStep,core.iter.range.UScalarStep.forward_checked,
   core.cmp.PartialOrdU32,core.clone.CloneU32,bound]
 congr 3
 apply UScalar.eq_of_val_eq
 rw [value s bound]
 rfl

theorem exit : core.iter.range.IteratorRange.next core.iter.range.StepU32
    {start:=18#u32,«end»:=18#u32}=
    ok (none,{start:=18#u32,«end»:=18#u32}) := by
 simp [core.iter.range.IteratorRange.next,core.iter.range.StepU32,
   core.iter.range.UScalarStep,core.cmp.PartialOrdU32]

#print value
#print axioms value
#print active
#print axioms active
#print exit
#print axioms exit
end NJE_CountRange
