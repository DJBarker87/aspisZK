import NDO_JHe_Natives
import NDO_JHc_CorrectedOwnership
import RPz8_CPH_FixtureKeys
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkDistinct
open Aeneas Aeneas.Std Result ControlFlow S2W_D189Entry
open _root_.AdapterRw
attribute [local irreducible] JHb_Header.account JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint
def sizes : Nat → Nat
  | 0 => 58295
  | 1 => 1880
  | _ => 1768
abbrev account (n : Nat) := JHb_World.e1.snapshot n (sizes n) (sizes n)
def value : Array AdapterRw.Cuts.Account 3#usize := Array.make 3#usize [account 0,account 1,account 2]

theorem key_ne (base : Ops) (stage : VTop_Stages.Ops) (i j : Fin 3) (different : i≠j) :
    (JHe_Natives.sdk base stage).op36 (account i.val).key (account j.val).key=ok false := by
  change Hist_Authority.keyEq (CPH_RecordedKeys.key i.val) (CPH_RecordedKeys.key j.val)=_
  have h : CPH_RecordedKeys.key i.val≠CPH_RecordedKeys.key j.val := by
    intro same
    apply different
    apply Fin.ext
    exact CPH_RecordedKeys.injective i.val j.val (by omega) (by omega) same
  simp [Hist_Authority.keyEq,h]
#print axioms key_ne

theorem read0 : Array.index_usize value 0#usize=ok (account 0) := rfl
#print axioms read0

theorem inc0 : Usize.wrapping_add 0#usize 1#usize=1#usize := by
  apply UScalar.eq_of_val_eq
  exact Port3_Wrapping.increment 0#usize (by decide)
#print axioms inc0

theorem read1 : Array.index_usize value 1#usize=ok (account 1) := rfl
#print axioms read1

theorem inc1 : Usize.wrapping_add 1#usize 1#usize=2#usize := by
  apply UScalar.eq_of_val_eq
  exact Port3_Wrapping.increment 1#usize (by decide)
#print axioms inc1

theorem read2 : Array.index_usize value 2#usize=ok (account 2) := rfl
#print axioms read2

theorem inc2 : Usize.wrapping_add 2#usize 1#usize=3#usize := by
  apply UScalar.eq_of_val_eq
  exact Port3_Wrapping.increment 2#usize (by decide)
#print axioms inc2

theorem inner0_end (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHe_Natives.sdk base stage)
      value 0#usize 0#usize=ok (done none) := by rfl
#print axioms inner0_end

theorem inner0 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 (JHe_Natives.sdk base stage)
      value 0#usize 0#usize=ok none := by
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [inner0_end,bind_tc_ok]
#print axioms inner0

theorem outer0 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHe_Natives.sdk base stage)
      value 0#usize=ok (cont 1#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),inner0,bind_tc_ok]
  simp only [lift,inc0,bind_tc_ok]
#print axioms outer0

theorem inner1_0 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHe_Natives.sdk base stage)
      value 1#usize 0#usize=ok (cont 1#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
  rw [if_pos (by decide),read0,bind_tc_ok,read1]
  simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok]
  rw [key_ne base stage ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide),bind_tc_ok]
  simp only [Bool.false_eq_true,if_false,lift,inc0,bind_tc_ok]
#print axioms inner1_0

theorem inner1_end (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHe_Natives.sdk base stage)
      value 1#usize 1#usize=ok (done none) := by rfl
#print axioms inner1_end

theorem inner1 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 (JHe_Natives.sdk base stage)
      value 1#usize 0#usize=ok none := by
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [inner1_0,bind_tc_ok]
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [inner1_end,bind_tc_ok]
#print axioms inner1

theorem outer1 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHe_Natives.sdk base stage)
      value 1#usize=ok (cont 2#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),inner1,bind_tc_ok]
  simp only [lift,inc1,bind_tc_ok]
#print axioms outer1

theorem inner2_0 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHe_Natives.sdk base stage)
      value 2#usize 0#usize=ok (cont 1#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
  rw [if_pos (by decide),read0,bind_tc_ok,read2]
  simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok]
  rw [key_ne base stage ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide),bind_tc_ok]
  simp only [Bool.false_eq_true,if_false,lift,inc0,bind_tc_ok]
#print axioms inner2_0

theorem inner2_1 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHe_Natives.sdk base stage)
      value 2#usize 1#usize=ok (cont 2#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
  rw [if_pos (by decide),read1,bind_tc_ok,read2]
  simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok]
  rw [key_ne base stage ⟨1,by decide⟩ ⟨2,by decide⟩ (by decide),bind_tc_ok]
  simp only [Bool.false_eq_true,if_false,lift,inc1,bind_tc_ok]
#print axioms inner2_1

theorem inner2_end (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHe_Natives.sdk base stage)
      value 2#usize 2#usize=ok (done none) := by rfl
#print axioms inner2_end

theorem inner2 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 (JHe_Natives.sdk base stage)
      value 2#usize 0#usize=ok none := by
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [inner2_0,bind_tc_ok]
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [inner2_1,bind_tc_ok]
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [inner2_end,bind_tc_ok]
#print axioms inner2

theorem outer2 (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHe_Natives.sdk base stage)
      value 2#usize=ok (cont 3#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),inner2,bind_tc_ok]
  simp only [lift,inc2,bind_tc_ok]
#print axioms outer2

theorem outer_end (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHe_Natives.sdk base stage)
      value 3#usize=ok (done none) := by rfl
#print axioms outer_end

theorem source (base : Ops) (stage : VTop_Stages.Ops) :
    r1_pool_adapter.owned.require_distinct_accounts (JHe_Natives.sdk base stage) value=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts
  have loop : r1_pool_adapter.owned.require_distinct_accounts_loop0 (JHe_Natives.sdk base stage)
      value 0#usize=ok none := by
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [outer0,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [outer1,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [outer2,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [outer_end,bind_tc_ok]
  rw [loop,bind_tc_ok]
#print axioms source
end AspisR1.JHe_SdkDistinct
end
