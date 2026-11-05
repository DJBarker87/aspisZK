import NHG_SelectedClaim
import NHG_AddWords
import NDO_JGa_Reconstruct
import NDO_JFy_SumHigh
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
 FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root level=
 Array.index_usize FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 level := by
 unfold FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root
 cases get : Array.index_usize
   FIq_Native.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 level with
 | fail e => rfl
 | div => rfl
 | ok row => exact AspisR1.FIy_EmptyRootMap.value row

theorem scalar_total (v : Variant) (present : Bool) (input output transfer withdrawal : Q)
 (ho : NHG_AddWords.NCanonical output) (ht : NHG_AddWords.NCanonical transfer)
 (hw : NHG_AddWords.NCanonical withdrawal) :
 ∃ result,FIq_Native.pool_v1.pair_forest_semantic_terminal.scalar_lanes v present input output transfer withdrawal=ok result ∧
 result.val[0]'(by simpa [result.property])=input := by
 rw [scalar_source]
 cases v with
 | PrivateTransfer =>
   obtain ⟨next,call,_,_⟩:=NHG_AddWords.nq_add output transfer ho ht
   refine ⟨Array.make 2#usize [input,next],?_,rfl⟩
   simp only [scalarBody,call,bind_tc_ok,ite_true]
 | Withdrawal =>
   cases present with
   | false => exact ⟨Array.make 2#usize [input,output],rfl,rfl⟩
   | true =>
     obtain ⟨next,call,_,_⟩:=NHG_AddWords.nq_add output withdrawal ho hw
     refine ⟨Array.make 2#usize [input,next],?_,rfl⟩
     simp only [scalarBody,call,bind_tc_ok,ite_true]

def initialBody (v : Variant) (a b c : Q) : Result (Q×Q×Q×Q) :=
 match v with
 | .PrivateTransfer => do
   let ab←FIq_Native.field.QM31.add a b
   ok (a,FIq_Native.field.QM31.ZERO,ab,c)
 | .Withdrawal => do
   let ab←FIq_Native.field.QM31.add a b
   let abc←FIq_Native.field.QM31.add ab c
   ok (FIq_Native.field.QM31.ZERO,abc,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO)

theorem initial_source (v : Variant) (a b c : Q) :
 FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors v a b c=initialBody v a b c := by
 cases v <;> rfl

theorem reconstruct_step (acc bit : Q) :
 AspisR1.FIx_ReconstructStep.callback.call_mut () (acc,bit)=(do
  let twice←FIq_Native.field.QM31.add acc acc
  let out←FIq_Native.field.QM31.add twice bit
  ok (out,())) := rfl

theorem reconstruct_result (view : Array Q 16#usize) (canonical : AspisR1.FIw_ArrayValue.canonical view) :
 ∃ out,FIq_Native.pool_v1.pair_forest_semantic_terminal.reconstruct_10 view=ok out ∧
 AspisR1.FIv_NativeValue.Canon out :=
 WP.spec_imp_exists (AspisR1.JGa_Reconstruct.source view canonical)

theorem sum_result (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors)
 (ranges : Slice (core.ops.range.Range Usize))
 (bounds : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64)
 (canonical : AspisR1.FIw_ArrayValue.canonical s.high) :
 ∃ out,FIq_Native.pool_v1.pair_forest_semantic_terminal.sum_high s ranges=ok out ∧
 AspisR1.FIv_NativeValue.Canon out :=
 AspisR1.JFy_SumHigh.source s ranges bounds canonical

#print axioms initial_source
#print axioms reconstruct_step
#print axioms reconstruct_result
#print axioms sum_result
#print axioms scalar_total
#print axioms scalar_source
#print axioms carry_total
#print axioms carry_result
#print axioms empty_source
#print FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
end AspisR1.NHG_ExtraLeaves
