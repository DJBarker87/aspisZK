import NHG_SelectedClaim
import NHG_AddWords
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHG_ExtraLeaves
abbrev Q := FIq_Native.field.QM31
abbrev Variant := FIq_Native.pool_v1.pair_forest_semantic_terminal.CompiledVariant
abbrev carryLoop := FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop

def scalarBody (v : Variant) (present : Bool) (input output transfer withdrawal : Q) :
 Result (Array Q 2#usize) :=
 match v with
 | .PrivateTransfer => do
   let next←FIq_Native.field.QM31.add output transfer
   ok (Array.make 2#usize [input,next])
 | .Withdrawal => if present then do
   let next←FIq_Native.field.QM31.add output withdrawal
   ok (Array.make 2#usize [input,next])
  else ok (Array.make 2#usize [input,output])

theorem scalar_source (v : Variant) (present : Bool) (input output transfer withdrawal : Q) :
 FIq_Native.pool_v1.pair_forest_semantic_terminal.scalar_lanes v present input output transfer withdrawal=
 scalarBody v present input output transfer withdrawal := by
 cases v <;> cases present <;> rfl

theorem carry_total (fuel : Nat) (index : U64) (carry : Usize)
 (span : carry.val+fuel=20) : ∃ out,carryLoop index carry=ok out := by
 induction fuel generalizing index carry with
 | zero =>
   have stop : ¬carry<20#usize := by change ¬carry.val<20;omega
   refine ⟨carry,?_⟩
   rw [carryLoop,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,if_neg stop]
 | succ fuel ih =>
   have active : carry<20#usize := by change carry.val<20;omega
   by_cases even : (index &&& 1#u64)=0#u64
   · refine ⟨carry,?_⟩
     rw [carryLoop,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,if_pos active]
     simp only [lift,bind_tc_ok,even,ite_true]
   · obtain ⟨nextIndex,shift,shiftSpec⟩:=WP.spec_imp_exists
      (UScalar.ShiftRight_spec index 1#u32 (by decide))
     have addSpec : (carry+1#usize : Result Usize) ⦃z=>z.val=carry.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
     obtain ⟨nextCarry,increment,value⟩:=WP.spec_imp_exists addSpec
     obtain ⟨out,tail⟩:=ih nextIndex nextCarry (by omega)
     refine ⟨out,?_⟩
     rw [carryLoop,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,if_pos active]
     simp only [lift,bind_tc_ok,if_neg even,shift,increment]
     exact tail

theorem carry_result (index : U64) :
 ∃ out,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry index=ok out ∧
 out.val=R0P.digestCarry index.val ∧ out.val≤20 := by
 obtain ⟨out,call⟩:=carry_total 20 index 0#usize (by rfl)
 have source : FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry index=ok out := call
 exact ⟨out,source,AspisR1.FIy_Carry.caller index out source⟩

theorem empty_source (level : Usize) :
 FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root level=(do
  let roots←FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  Array.index_usize roots level) := by
 unfold FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root
 cases h : FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 with
 | fail e => rfl
 | div => rfl
 | ok roots =>
   simp only [h,bind_tc_ok]
   cases get : Array.index_usize roots level with
   | fail e => rfl
   | div => rfl
   | ok row => exact AspisR1.FIy_EmptyRootMap.value row

#print axioms scalar_source
#print axioms carry_total
#print axioms carry_result
#print axioms empty_source
#print FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
end AspisR1.NHG_ExtraLeaves
