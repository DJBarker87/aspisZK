import RPu_FIp_ArrayValue
import RPu_FIo_ArrayBack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_ArraySetValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)

theorem same {N : Usize} (a : Array NE N) (i : Usize) (z : NE) (hi : i.val<N.val) :
    FIp_ArrayValue.value (Aeneas.Std.Array.set a i z) i.val=decodeWide (wide z) := by
  have h : i.val<a.val.length := by simpa only [a.property] using hi
  simp only [FIp_ArrayValue.value,Aeneas.Std.Array.set,List.getElem?_set_self h]

theorem other {N : Usize} (a : Array NE N) (i : Usize) (z : NE) (j : Nat) (ne : i.val≠j) :
    FIp_ArrayValue.value (Aeneas.Std.Array.set a i z) j=FIp_ArrayValue.value a j := by
  simp only [FIp_ArrayValue.value,Aeneas.Std.Array.set,List.getElem?_set_ne ne]

theorem back {N : Usize} (a : Array NE N) (i : Usize) (old : NE) (back : NE → Array NE N)
    (run : Array.index_mut_usize a i=ok (old,back)) : back=Aeneas.Std.Array.set a i := by
  unfold Array.index_mut_usize at run
  obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact (congrArg Prod.snd (Result.ok.inj run)).symm

#print axioms same
#print axioms other
#print axioms back
end AspisR1.FIp_ArraySetValue
end
