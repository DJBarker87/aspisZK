import S9ConstructorV3VectorMeaningV1
import S9ReverseRangeProgressV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3CarryMeaningStepV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1

def SuffixMeaning (p : Nat → ExactQM) (remaining : Nat) : Nat → ExactQM :=
  fun i => if i < remaining then p i else successorPoint p i

/-- One current source reverse-carry step preserves the symbolic processed-
suffix invariant used by retained ProverCommitSuccessorPoint49.successor_value. -/
theorem carry_step_meaning
    (p : Nat → ExactQM) (z successor successorOut : Vector)
    (iter iterNext : ReverseRange) (carry carryOut : Q)
    (hz : VectorCanonical z) (hzMean : Meaning z p)
    (hs : VectorCanonical successor) (hc : Can carry)
    (hstart : iter.iter.start.val=0) (hend : iter.iter.end.val≤10)
    (hcarry : decode carry=succCarry p (10-iter.iter.end.val))
    (hmeaning : Meaning successor (SuffixMeaning p iter.iter.end.val))
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.cont (iterNext,successorOut,carryOut))) :
    iterNext.iter.start.val=0 ∧ iterNext.iter.end.val≤10 ∧
      VectorCanonical successorOut ∧ Can carryOut ∧
      decode carryOut=succCarry p (10-iterNext.iter.end.val) ∧
      Meaning successorOut (SuffixMeaning p iterNext.iter.end.val) := by
  obtain ⟨coordinate,bit,cell,hnext,hbit,hupdate,hccarry,hccell,hdcarry,hdcell⟩ :=
    carry_body_success_exact z successor successorOut iter iterNext carry carryOut hz hc hbody
  obtain ⟨hlt,hcoord,hstarts,hends⟩ :=
    AspisR1S9ReverseRangeProgressV1.reverse_next_some_progress iter iterNext coordinate hnext
  have hcoordVal : coordinate.val = iterNext.iter.end.val := by
    rw [hcoord,AspisR1S9ReverseRangeProgressV1.wrapping_sub_one_val _ (by omega)]
    omega
  have hbitVal := hzMean coordinate bit hbit
  have hshift : 10-iter.iter.end.val=9-iterNext.iter.end.val := by omega
  have hcarryNext : decode carryOut=succCarry p (10-iterNext.iter.end.val) := by
    rw [hdcarry,hbitVal,hcarry,hshift,hcoordVal,
      carry_step p iterNext.iter.end.val (by omega)]
  have hcellVal : decode cell=successorPoint p iterNext.iter.end.val := by
    rw [hdcell,hbitVal,hcarry,hcoordVal,hshift]
    rfl
  have hout := update_meaning successor successorOut coordinate cell
    (SuffixMeaning p iter.iter.end.val) hmeaning hupdate
  have hmeaningNext : Meaning successorOut (SuffixMeaning p iterNext.iter.end.val) := by
    have hfun : Function.update (SuffixMeaning p iter.iter.end.val) coordinate.val (decode cell) =
        SuffixMeaning p iterNext.iter.end.val := by
      funext i
      by_cases he : i=coordinate.val
      · subst i
        rw [Function.update_self,hcoordVal,hcellVal]
        simp only [SuffixMeaning,lt_self_iff_false,if_false]
      · rw [Function.update_of_ne he]
        unfold SuffixMeaning
        have he' : i≠iterNext.iter.end.val := by simpa only [hcoordVal] using he
        by_cases hi : i < iterNext.iter.end.val
        · rw [if_pos hi,if_pos (by omega)]
        · rw [if_neg hi,if_neg (by omega)]
    rw [hfun] at hout
    exact hout
  have hcan := carry_body_success_canonical z successor successorOut iter iterNext carry carryOut hz hs hc hbody
  exact ⟨by simpa only [hstarts] using hstart,by omega,hcan.1,hccarry,hcarryNext,hmeaningNext⟩

#print axioms carry_step_meaning
end AspisR1S9ConstructorV3CarryMeaningStepV1
