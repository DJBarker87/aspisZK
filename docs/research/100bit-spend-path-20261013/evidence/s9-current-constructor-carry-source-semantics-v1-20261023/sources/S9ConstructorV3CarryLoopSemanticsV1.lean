import S9ConstructorV3CarryMeaningStepV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3CarryLoopSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3CarryMeaningStepV1
private theorem body_done_same_successor
    (z successor out : Vector) (iter : ReverseRange) (carry : Q)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.done out)) : out = successor := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done successor : ControlFlow (ReverseRange × Vector × Q) Vector) =
      ok (ControlFlow.done out : ControlFlow (ReverseRange × Vector × Q) Vector) at hbody
    exact (ControlFlow.done.inj (Result.ok.inj hbody)).symm
  | some coordinate =>
    obtain ⟨bit, hbit, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨product, hp, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨sum, hsum, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨twice, htwice, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨cell, hcell, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨out, hupdate, hbody⟩ := bind_success_inv _ _ _ hbody
    cases hbody

private theorem body_done_stopped
    (z successor out : Vector) (iter : ReverseRange) (carry : Q)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.done out)) : iter.iter.end.val ≤ iter.iter.start.val := by
  by_contra hn
  have hnext := AspisR1S9ReverseRangeProgressV1.reverse_next_step iter (by omega)
  unfold AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body at hbody
  rw [hnext] at hbody
  simp only [bind_tc_ok] at hbody
  obtain ⟨bit,hbit,hbody⟩ := bind_success_inv _ _ _ hbody
  obtain ⟨product,hp,hbody⟩ := bind_success_inv _ _ _ hbody
  obtain ⟨sum,hsum,hbody⟩ := bind_success_inv _ _ _ hbody
  obtain ⟨twice,htwice,hbody⟩ := bind_success_inv _ _ _ hbody
  obtain ⟨cell,hcell,hbody⟩ := bind_success_inv _ _ _ hbody
  obtain ⟨out,hupdate,hbody⟩ := bind_success_inv _ _ _ hbody
  cases hbody

/-- Complete accepted-run exact meaning of the actual reverse carry loop.
The processed suffix/carry premises describe its INITIAL state. The same-call
step witnesses are all derived internally. -/
theorem carry_loop_success_exact
    (p : Nat → ExactQM) (z successor out : Vector) (iter : ReverseRange) (carry : Q)
    (hz : VectorCanonical z) (hzMean : Meaning z p)
    (hs : VectorCanonical successor) (hc : Can carry)
    (hstart : iter.iter.start.val=0) (hend : iter.iter.end.val≤10)
    (hcarry : decode carry=succCarry p (10-iter.iter.end.val))
    (hmeaning : Meaning successor (SuffixMeaning p iter.iter.end.val))
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop
      iter z successor carry = .ok out) :
    VectorCanonical out ∧ Meaning out (successorPoint p) := by
  let step : (ReverseRange × Vector × Q) → Result (ControlFlow (ReverseRange × Vector × Q) Vector) :=
    fun s => AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z s.1 s.2.1 s.2.2
  let measure : (ReverseRange × Vector × Q) → Nat := fun s => s.1.iter.end.val
  let inv : (ReverseRange × Vector × Q) → Prop := fun s =>
    s.1.iter.start.val=0 ∧ s.1.iter.end.val≤10 ∧
      VectorCanonical s.2.1 ∧ Can s.2.2 ∧
      decode s.2.2=succCarry p (10-s.1.iter.end.val) ∧
      Meaning s.2.1 (SuffixMeaning p s.1.iter.end.val)
  let post : Vector → Prop := fun a => VectorCanonical a ∧ Meaning a (successorPoint p)
  have hd : ∀ s result, inv s → step s = .ok (.done result) → post result := by
    rintro ⟨it,buf,c⟩ result hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨hstart,hend,hbuf,hc,hcarry,hmeaning⟩
    have he := body_done_same_successor z buf result it c hb
    have hstop := body_done_stopped z buf result it c hb
    have hz0 : it.iter.end.val=0 := by omega
    subst result
    refine ⟨hbuf,?_⟩
    have hzero : SuffixMeaning p 0=successorPoint p := by
      funext i
      simp only [SuffixMeaning,Nat.not_lt_zero,if_false]
    rw [hz0,hzero] at hmeaning
    exact hmeaning
  have hcstep : ∀ s s', inv s → step s = .ok (.cont s') → inv s' := by
    rintro ⟨it,buf,c⟩ ⟨it1,buf1,c1⟩ hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨hstart,hend,hbuf,hc,hcarry,hmeaning⟩
    exact carry_step_meaning p z buf buf1 it it1 c c1 hz hzMean hbuf hc
      hstart hend hcarry hmeaning hb
  have hdec : ∀ s s', step s = .ok (.cont s') → measure s' < measure s := by
    rintro ⟨it,buf,c⟩ ⟨it1,buf1,c1⟩ hb
    obtain ⟨coordinate,bit,product,sum,twice,cell,hnext,hrest⟩ :=
      carry_body_success_has_execution z buf buf1 it it1 c c1 hb
    obtain ⟨hlt,hd,hstart,hend⟩ :=
      AspisR1S9ReverseRangeProgressV1.reverse_next_some_progress it it1 coordinate hnext
    dsimp only [measure]
    omega
  have hloop' : Aeneas.Std.loop step (iter,successor,carry)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property step measure inv post
    hd hcstep hdec (iter,successor,carry) out
    ⟨hstart,hend,hs,hc,hcarry,hmeaning⟩ hloop'

#print axioms carry_loop_success_exact
end AspisR1S9ConstructorV3CarryLoopSemanticsV1
