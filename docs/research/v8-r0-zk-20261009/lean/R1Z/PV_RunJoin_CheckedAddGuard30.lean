import R1Z.PV_RunJoin_CheckedAdd30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CheckedAddGuard30
open Aeneas Aeneas.Std Result

theorem positive (n : U32) (hn : n ≠ 0#u32) : 0<n.val := by
  have hv : n.val≠0 := by
    intro h
    apply hn
    exact UScalar.eq_of_val_eq h
  omega
#print axioms positive

theorem value (a b c : U32) {o : Option U32} {bit : Bool}
    (ho : lift (U32.checked_add a b) = ok o)
    (hb : PV_RunJoin_Outer30.core.option.Option.Insts.CoreCmpPartialEqOption.ne
      core.cmp.PartialEqU32 o (some c) = ok bit)
    (hp : ¬ bit=true) : a.val+b.val=c.val := by
  change ok (U32.checked_add a b) = ok o at ho
  cases Result.ok.inj ho
  have hz : bit=false := Bool.eq_false_iff.mpr hp
  rw [hz] at hb
  exact PV_RunJoin_CheckedAdd30.value a b c ((PV_RunJoin_CheckedAdd30.option_ne_false _ _).mp hb)
#print axioms value
end R1Z.PV_RunJoin_CheckedAddGuard30
