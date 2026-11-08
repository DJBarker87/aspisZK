import NNG_ProjectAccounts345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ArgsPort345
open Aeneas Aeneas.Std RSL

theorem count (a : TX1_345.Args) (good : TX1_345.badRoute a=false) : a.accounts.length=3 := by
 by_cases same : a.accounts.length=3
 · exact same
 · have mismatch : (a.accounts.length !=3)=true := bne_iff_ne.mpr same
   unfold TX1_345.badRoute at good
   rw [mismatch,Bool.or_true] at good
   cases good
#print axioms count

theorem route (a : TX1_345.Args) (good : TX1_345.badRoute a=false) :
 a.data=[3,10] ∨ a.data=[3,11] := by
 by_cases first : a.data=[3,10]
 · exact Or.inl first
 · by_cases second : a.data=[3,11]
   · exact Or.inr second
   · unfold TX1_345.badRoute at good
     simp only [show (a.data ==[3,10])=false from beq_eq_false_iff_ne.mpr first,
       show (a.data ==[3,11])=false from beq_eq_false_iff_ne.mpr second,
       Bool.false_or,Bool.not_false,Bool.true_or] at good
     cases good
#print axioms route

theorem bounds (a : TX1_345.Args) (good : TX1_345.badRoute a=false) :
 NNG_ReifyCore345.ArgsBounds (NNG_ProjectAccounts345.args a) := by
 constructor
 · change (a.accounts.map NNG_ProjectAccounts345.account).length≤Usize.max
   rw [List.length_map,count a good]
   scalar_tac
 · constructor
   · change a.data.length≤Usize.max
     rcases route a good with h|h <;> rw [h] <;> change 2≤Usize.max <;> scalar_tac
   · intro acc member
     obtain ⟨original,_,same⟩ := List.mem_map.mp member
     subst acc
     exact NNG_ProjectAccounts345.bounds original
#print axioms bounds
end AspisR1.NNG_ArgsPort345
