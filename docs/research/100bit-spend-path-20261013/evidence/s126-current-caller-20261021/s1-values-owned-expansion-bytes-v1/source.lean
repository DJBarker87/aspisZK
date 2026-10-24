import S1ValuesOwnedExpansionFormulaV1
import S1ValuesOwnedOuterStepTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedExpansionBytes
open Aeneas Aeneas.Std Result ControlFlow AspisS1ValuesOwned
open AspisS1ValuesOwnedExpansionFormula
abbrev Buffer := alloc.vec.Vec U8

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (m >>= k)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h
private theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b)=ok v) :
    ∃ a b,m=ok (a,b) ∧ k a b=ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => cases h
  | div => cases h

theorem step_bytes (input output next updated : Buffer) (count chunk chunk1 : Usize)
    (active : chunk.val<count.val)
    (inputRange : count.val*16 ≤ input.length)
    (outputRange : count.val*32 ≤ output.length)
    (call : values_owned_reference_loop.body count input output chunk=ok (.cont (next,updated,chunk1))) :
    next=input ∧ updated.length=output.length ∧ chunk1.val=chunk.val+1 ∧
    AspisS1ValuesOwnedChunkFormula.Partial input output updated chunk.val 16 := by
  have test : chunk<count := by scalar_tac
  unfold values_owned_reference_loop.body at call
  simp only [if_pos test] at call
  obtain ⟨i,o,hcopy,call⟩ := pair_success _ _ _ call
  obtain ⟨c,hinc,call⟩ := bind_success _ _ _ call
  have triple := ControlFlow.cont.inj (Result.ok.inj call)
  have si : i=next := congrArg Prod.fst triple
  have so : o=updated := congrArg (fun p => p.2.1) triple
  have sc : c=chunk1 := congrArg (fun p => p.2.2) triple
  subst i
  subst o
  subst c
  have innerInput : chunk.val*16+16 ≤ input.length := by omega
  have innerOutput : chunk.val*32+32 ≤ output.length := by omega
  obtain ⟨kept,length,bytes⟩ := AspisS1ValuesOwnedChunkBytes.chunk_bytes
    input output next updated chunk innerInput innerOutput hcopy
  have advance := AspisS1FrameArithmetic.add_value chunk 1#usize chunk1 hinc
  exact ⟨kept,length,by scalar_tac,bytes⟩

/-- Complete emitted outer loop, exact contents of every output byte. -/
theorem loop_bytes (input original next updated : Buffer) (count : Usize)
    (inputRange : count.val*16 ≤ input.length)
    (outputRange : count.val*32 ≤ original.length)
    (call : values_owned_reference_loop input original count 0#usize=ok (next,updated)) :
    next=input ∧ updated.length=original.length ∧ Partial input original updated count.val := by
  unfold values_owned_reference_loop at call
  apply AspisS1LoopSafety.accepted
    (fun (i,o,c) => values_owned_reference_loop.body count i o c)
    (fun (i,o,c) => i=input ∧ o.length=original.length ∧ c.val≤count.val ∧
      Partial input original o c.val)
    (fun (i,o) => i=input ∧ o.length=original.length ∧ Partial input original o count.val)
    _ (input,original,0#usize) ⟨rfl,rfl,by scalar_tac,initial input original⟩
    (next,updated) call
  intro state inv r step
  rcases state with ⟨i,o,c⟩
  rcases inv with ⟨sameInput,sameLength,chunkBound,held⟩
  subst i
  have outputBound : count.val*32 ≤ o.length := by rw [sameLength];exact outputRange
  by_cases active : c.val<count.val
  · obtain ⟨i1,o1,c1,source,_,_,_⟩ :=
      AspisS1ValuesOwnedTotal.outer_step_total input o count c active inputRange outputBound
    have same : r=.cont (i1,o1,c1) := Result.ok.inj (step.symm.trans source)
    subst r
    obtain ⟨inputKept,lengthKept,advanceChunk,writes⟩ :=
      step_bytes input o i1 o1 count c c1 active inputRange outputBound source
    refine ⟨inputKept,lengthKept.trans sameLength,by omega,?_⟩
    rw [advanceChunk]
    exact advance input original o o1 c.val held writes
  · have test : ¬c<count := by scalar_tac
    unfold values_owned_reference_loop.body at step
    simp only [if_neg test] at step
    have same := Result.ok.inj step
    subst r
    have lastChunk : c.val=count.val := by omega
    exact ⟨rfl,sameLength,by simpa only [lastChunk] using held⟩

#print axioms step_bytes
#print axioms loop_bytes
end AspisS1ValuesOwnedExpansionBytes
