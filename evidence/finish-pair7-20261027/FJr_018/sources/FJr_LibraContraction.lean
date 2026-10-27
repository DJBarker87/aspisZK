import FJf_ArraySlots
import FJc_LibraFrame
import FJc_InactiveCoefficientsModel
import FIp_RangeNone
import FIo_Constants
import FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraContraction
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open scoped BigOperators
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev State := FIo_RangeNext.Range × Array NE 7#usize

def term (f : Slice U8) (libra : Array NE 4#usize) (j : Nat) : FE :=
  FJc_InactiveCoefficientsModel.field f j * FIp_ArrayValue.value libra j

def sumPrefix (f : Slice U8) (libra : Array NE 4#usize) : Nat → FE
  | 0=>0
  | n+1=>sumPrefix f libra n+term f libra n

def Inv (f : Slice U8) (libra : Array NE 4#usize) (s : State) : Prop :=
  s.1.end.val=4 ∧ s.1.start.val≤4 ∧
    (∃ x,s.2.val[4]?=some x ∧ FIo_WideValues.Canon x) ∧
    FIp_ArrayValue.value s.2 4=sumPrefix f libra s.1.start.val

def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem step (f : Slice U8) (libra : Array NE 4#usize) (cl : FIo_ArrayCanon.Holds libra)
    (s : State) (inv : Inv f libra s) (result : ControlFlow State (Array NE 7#usize))
    (run : FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2=ok result) :
    match result with
    | .done out=> FIp_ArrayValue.value out 4=sumPrefix f libra 4
    | .cont next=>Inv f libra next ∧ measure next<measure s := by
  rcases s with ⟨iter,parts⟩
  rcases inv with ⟨he,hs,⟨old0,hslot,cold⟩,value⟩
  change iter.end.val=4 at he
  change iter.start.val≤4 at hs
  change FIp_ArrayValue.value parts 4=sumPrefix f libra iter.start.val at value
  change parts.val[4]?=some old0 at hslot
  unfold FIo_Native.weights.Weights.pair_loop16.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none=>
    cases Result.ok.inj run
    have stop := FIp_RangeNone.none_next iter cursor hn
    have eq : iter.start.val=4 := by omega
    simpa only [eq] using value
  | some j=>
    obtain ⟨old,hold,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨fv,hfv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨lv,hlv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨sum,hsum,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hupdated,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have pr := FIo_RangeNext.some_next iter cursor j hn
    have same : old=old0 := by
      have slot := FJc_ReadSlot.slot parts 4#usize old hold
      change parts.val[4]?=some old at slot
      rw [hslot] at slot
      exact (Option.some.inj slot).symm
    have cproduct := FIo_WideMulValues.mul fv lv product
      (FIo_FieldCanonical.field f j fv hfv) (FIo_ArrayCanon.read libra j lv cl hlv) hproduct
    have csum := FIo_WideValues.add old product sum (same.symm ▸ cold) cproduct.1 hsum
    refine ⟨?_,?_⟩
    · change cursor.end.val=4 ∧ cursor.start.val≤4 ∧ _ ∧ _
      refine ⟨by rw [pr.2.1];exact he,by rw [pr.2.2.1];omega,?_,?_⟩
      · refine ⟨sum,?_,csum.1⟩
        rw [FJf_ArraySlots.update_slot parts updated 4#usize sum hupdated 4]
        rfl
      · rw [FJc_ArrayUpdateValue.value parts updated 4#usize sum 4 hupdated]
        simp only [show (4#usize).val=4 from by decide,if_true]
        rw [csum.2,cproduct.2,←FIp_ArrayValue.read parts 4#usize old hold,
          ←FIp_ArrayValue.read libra j lv hlv,←FJc_InactiveCoefficientsModel.field_read f j fv (by rw [pr.1];omega) hfv]
        change FIp_ArrayValue.value parts 4+term f libra j.val=sumPrefix f libra cursor.start.val
        rw [value,pr.1,pr.2.2.1,sumPrefix]
    · simp only [measure,pr.2.1,pr.2.2.1];omega

theorem value (f : Slice U8) (libra : Array NE 4#usize) (cl : FIo_ArrayCanon.Holds libra)
    (parts out : Array NE 7#usize)
    (zero : parts.val[4]?=some FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)
    (run : FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f parts libra=ok out) :
    FIp_ArrayValue.value out 4=sumPrefix f libra 4 := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2)
    (Inv f libra) (fun a=>FIp_ArrayValue.value a 4=sumPrefix f libra 4)
    measure (fun s h r hr=>by cases r <;> exact step f libra cl s h _ hr)
    ({start:=0#usize,«end»:=4#usize},parts) out
    ⟨rfl,by change (0:Nat)≤4;omega,⟨_,zero,FIo_Constants.zero.1⟩,
      by simp only [FIp_ArrayValue.value,zero,FIo_Constants.zero.2,sumPrefix];rfl⟩ run

theorem sumPrefix_sum (f : Slice U8) (libra : Array NE 4#usize) (n : Nat) :
    sumPrefix f libra n=∑ j∈Finset.range n,term f libra j := by
  induction n with
  | zero=>simp only [sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih=>rw [sumPrefix,Finset.sum_range_succ,ih]

#print axioms sumPrefix_sum
#print axioms step
#print axioms value
end AspisR1.FJr_LibraContraction
end
