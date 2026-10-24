import S1ValuesOwnedModelV1
import S1LoopSafetyV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedFrame
open Aeneas Aeneas.Std Result ControlFlow AspisS1ValuesOwned
abbrev Buffer := alloc.vec.Vec U8
abbrev State := Buffer × Buffer × Usize
abbrev Exit := Buffer × Buffer

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

theorem read_frame (input next : Buffer) (index : Usize) (value : U8)
    (call : read_input input index=ok (value,next)) : next=input := by
  unfold read_input at call
  obtain ⟨got,hgot,call⟩ := bind_success _ _ _ call
  exact (congrArg Prod.snd (Result.ok.inj call)).symm

theorem write_length (output updated : Buffer) (index : Usize) (value : U8)
    (call : write_output output index value=ok updated) :
    updated.length=output.length := by
  unfold write_output at call
  simp only [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at call
  cases indexed : alloc.vec.Vec.index_usize output index with
  | fail e => simp only [indexed] at call; cases call
  | div => simp only [indexed] at call; cases call
  | ok old =>
    simp only [indexed,bind_tc_ok] at call
    have same := Result.ok.inj call
    subst updated
    exact alloc.vec.Vec.set_length output index value

def Frame (input : Buffer) (size : Nat) : ControlFlow State Exit → Prop
  | .cont (next,output,_) => next=input ∧ output.length=size
  | .done (next,output) => next=input ∧ output.length=size

theorem chunk_body_frame (chunk byte : Usize) (input output : Buffer)
    (r : ControlFlow State Exit)
    (call : copy_chunk_loop.body chunk input output byte=ok r) :
    Frame input output.length r := by
  unfold copy_chunk_loop.body at call
  split at call
  · obtain ⟨i,hi,call⟩ := bind_success _ _ _ call
    obtain ⟨i1,hi1,call⟩ := bind_success _ _ _ call
    obtain ⟨value,next,hread,call⟩ := pair_success _ _ _ call
    obtain ⟨i2,hi2,call⟩ := bind_success _ _ _ call
    obtain ⟨i3,hi3,call⟩ := bind_success _ _ _ call
    obtain ⟨out1,hout1,call⟩ := bind_success _ _ _ call
    obtain ⟨i4,hi4,call⟩ := bind_success _ _ _ call
    obtain ⟨i5,hi5,call⟩ := bind_success _ _ _ call
    obtain ⟨out2,hout2,call⟩ := bind_success _ _ _ call
    obtain ⟨byte1,hbyte1,call⟩ := bind_success _ _ _ call
    have same := Result.ok.inj call
    subst r
    exact ⟨read_frame input next i1 value hread,
      (write_length out1 out2 i5 _ hout2).trans (write_length output out1 i3 value hout1)⟩
  · have same := Result.ok.inj call
    subst r
    exact ⟨rfl,rfl⟩

theorem chunk_frame (input output next updated : Buffer) (chunk byte : Usize)
    (call : copy_chunk_loop input output chunk byte=ok (next,updated)) :
    next=input ∧ updated.length=output.length := by
  unfold copy_chunk_loop at call
  apply AspisS1LoopSafety.accepted
    (fun (i,o,b) => copy_chunk_loop.body chunk i o b)
    (fun (i,o,_) => i=input ∧ o.length=output.length)
    (fun (i,o) => i=input ∧ o.length=output.length) _
    (input,output,byte) ⟨rfl,rfl⟩ (next,updated) call
  intro state inv r step
  rcases state with ⟨i,o,b⟩
  have framed := chunk_body_frame chunk b i o r step
  cases r with
  | cont next =>
    rcases next with ⟨i1,o1,b1⟩
    exact ⟨framed.1.trans inv.1,framed.2.trans inv.2⟩
  | done value =>
    rcases value with ⟨i1,o1⟩
    exact ⟨framed.1.trans inv.1,framed.2.trans inv.2⟩

theorem outer_body_frame (count chunk : Usize) (input output : Buffer)
    (r : ControlFlow State Exit)
    (call : values_owned_reference_loop.body count input output chunk=ok r) :
    Frame input output.length r := by
  unfold values_owned_reference_loop.body at call
  split at call
  · obtain ⟨next,updated,hcopy,call⟩ := pair_success _ _ _ call
    obtain ⟨chunk1,hchunk1,call⟩ := bind_success _ _ _ call
    have same := Result.ok.inj call
    subst r
    exact chunk_frame input output next updated chunk 0#usize hcopy
  · have same := Result.ok.inj call
    subst r
    exact ⟨rfl,rfl⟩

theorem outer_frame (input output next updated : Buffer) (count chunk : Usize)
    (call : values_owned_reference_loop input output count chunk=ok (next,updated)) :
    next=input ∧ updated.length=output.length := by
  unfold values_owned_reference_loop at call
  apply AspisS1LoopSafety.accepted
    (fun (i,o,c) => values_owned_reference_loop.body count i o c)
    (fun (i,o,_) => i=input ∧ o.length=output.length)
    (fun (i,o) => i=input ∧ o.length=output.length) _
    (input,output,chunk) ⟨rfl,rfl⟩ (next,updated) call
  intro state inv r step
  rcases state with ⟨i,o,c⟩
  have framed := outer_body_frame count c i o r step
  cases r with
  | cont next =>
    rcases next with ⟨i1,o1,c1⟩
    exact ⟨framed.1.trans inv.1,framed.2.trans inv.2⟩
  | done value =>
    rcases value with ⟨i1,o1⟩
    exact ⟨framed.1.trans inv.1,framed.2.trans inv.2⟩

/-- Full extracted reference, every returned codec status. This is an
accepted-result frame, not a totality or unbounded native correspondence claim. -/
theorem reference_frame (input output next updated : Buffer)
    (status : core.result.Result Unit AspisR1CurrentCaller.compact.CodecError)
    (call : values_owned_reference input output=ok (status,next,updated)) :
    next=input ∧ updated.length=output.length := by
  unfold values_owned_reference at call
  obtain ⟨rem,hrem,call⟩ := bind_success _ _ _ call
  split at call
  · have same := Result.ok.inj call
    exact ⟨(congrArg (fun p => p.2.1) same).symm,
      congrArg (fun p => p.2.2.length) same.symm⟩
  · obtain ⟨twice,htwice,call⟩ := bind_success _ _ _ call
    split at call
    · have same := Result.ok.inj call
      exact ⟨(congrArg (fun p => p.2.1) same).symm,
        congrArg (fun p => p.2.2.length) same.symm⟩
    · obtain ⟨count,hcount,call⟩ := bind_success _ _ _ call
      obtain ⟨next1,updated1,hloop,call⟩ := pair_success _ _ _ call
      have same := Result.ok.inj call
      have ni : next1=next := congrArg (fun p => p.2.1) same
      have ou : updated1=updated := congrArg (fun p => p.2.2) same
      subst next1
      subst updated1
      exact outer_frame input output next updated count 0#usize hloop

#print axioms read_frame
#print axioms write_length
#print axioms chunk_frame
#print axioms outer_frame
#print axioms reference_frame
end AspisS1ValuesOwnedFrame
