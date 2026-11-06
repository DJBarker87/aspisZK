import FIy_Carry
set_option autoImplicit false
namespace AspisR1.NKR_DigestCarry
open Aeneas Aeneas.Std Result WP FIq_Native
abbrev loop := pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop
/-- Totality on the actual source twenty-bit carry loop, including carry20. -/
theorem total (fuel : Nat) (index : U64) (carry : Usize)
 (span : carry.val+fuel=20) :
 ∃ out,loop index carry=ok out ∧ out.val≤20 := by
 induction fuel generalizing index carry with
 | zero=>
   refine ⟨carry,?_,by omega⟩
   rw [loop,pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
     if_neg (show ¬carry<20#usize by change ¬carry.val<20;omega)]
 | succ fuel ih=>
   have bound : carry.val<20 := by omega
   rw [loop,pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
     if_pos (show carry<20#usize from bound)]
   simp only [lift,bind_tc_ok]
   split
   · exact ⟨carry,rfl,by omega⟩
   · obtain ⟨next,shift,_⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec index 1#u32 (by decide))
     obtain ⟨carry1,step,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=carry) (y:=1#usize) (by scalar_tac))
     obtain ⟨out,tail,ho⟩ := ih next carry1 (by change carry1.val=carry.val+1 at value;omega)
     exact ⟨out,by rw [shift,bind_tc_ok,step,bind_tc_ok];exact tail,ho⟩

theorem source (index : U64) :
 ∃ out,pool_v1.pair_forest_semantic_terminal.bounded_append_carry index=ok out ∧
 out.val=R0P.digestCarry index.val ∧ out.val≤20 := by
 obtain ⟨out,call,_⟩ := total 20 index 0#usize rfl
 exact ⟨out,call,(FIy_Carry.caller index out call).1,(FIy_Carry.caller index out call).2⟩
#print axioms total
#print axioms source
end AspisR1.NKR_DigestCarry
