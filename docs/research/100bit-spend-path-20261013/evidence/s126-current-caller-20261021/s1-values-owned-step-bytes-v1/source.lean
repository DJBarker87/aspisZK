import S1ValuesOwnedChunkFormulaV1
import S1FrameArithmeticV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedStepBytes
open Aeneas Aeneas.Std Result ControlFlow AspisS1ValuesOwned
open AspisS1FrameArithmetic AspisS1ValuesOwnedCell

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

/-- Exact byte effect of one actual emitted source step on full buffers. -/
theorem step_bytes (input output next updated : Buffer) (chunk byte byte1 : Usize)
    (active : byte.val<16)
    (inputRange : chunk.val*16+16 ≤ input.length)
    (outputRange : chunk.val*32+32 ≤ output.length)
    (call : copy_chunk_loop.body chunk input output byte=ok (.cont (next,updated,byte1))) :
    next=input ∧ updated.length=output.length ∧ byte1.val=byte.val+1 ∧
    ∀ j, updated.val[j]?=
      if j=chunk.val*32+16+byte.val then some 0#u8
      else if j=chunk.val*32+byte.val then input.val[chunk.val*16+byte.val]?
      else output.val[j]? := by
  have test : byte<16#usize := by scalar_tac
  unfold copy_chunk_loop.body at call
  simp only [if_pos test] at call
  obtain ⟨i,hi,call⟩ := bind_success _ _ _ call
  obtain ⟨i1,hi1,call⟩ := bind_success _ _ _ call
  obtain ⟨value,readNext,hread,call⟩ := pair_success _ _ _ call
  obtain ⟨i2,hi2,call⟩ := bind_success _ _ _ call
  obtain ⟨i3,hi3,call⟩ := bind_success _ _ _ call
  obtain ⟨out1,hout1,call⟩ := bind_success _ _ _ call
  obtain ⟨i4,hi4,call⟩ := bind_success _ _ _ call
  obtain ⟨i5,hi5,call⟩ := bind_success _ _ _ call
  obtain ⟨out2,hout2,call⟩ := bind_success _ _ _ call
  obtain ⟨b1,hb1,call⟩ := bind_success _ _ _ call
  have triple := ControlFlow.cont.inj (Result.ok.inj call)
  have sameInput : readNext=next := congrArg Prod.fst triple
  have sameOutput : out2=updated := congrArg (fun p => p.2.1) triple
  have sameByte : b1=byte1 := congrArg (fun p => p.2.2) triple
  subst readNext
  subst out2
  subst b1
  have iv := mul_value chunk 16#usize i hi
  have i1v := add_value i byte i1 hi1
  have i2v := mul_value chunk 32#usize i2 hi2
  have i3v := add_value i2 byte i3 hi3
  have i4v := add_value i2 16#usize i4 hi4
  have i5v := add_value i4 byte i5 hi5
  have b1v := add_value byte 1#usize byte1 hb1
  have inputBound : i1.val < input.length := by scalar_tac
  have lowBound : i3.val < output.length := by scalar_tac
  have outLength := AspisS1ValuesOwnedFrame.write_length output out1 i3 value hout1
  have highBound : i5.val < out1.length := by scalar_tac
  have readFacts := read_exact input next i1 value inputBound hread
  have finalLength := (AspisS1ValuesOwnedFrame.write_length out1 updated i5 0#u8 hout2).trans outLength
  refine ⟨readFacts.1,finalLength,by scalar_tac,?_⟩
  intro j
  rw [write_byte out1 updated i5 0#u8 highBound hout2 j,
    write_byte output out1 i3 value lowBound hout1 j]
  have lowAddress : i3.val=chunk.val*32+byte.val := by scalar_tac
  have highAddress : i5.val=chunk.val*32+16+byte.val := by scalar_tac
  have sourceAddress : i1.val=chunk.val*16+byte.val := by scalar_tac
  have inputByte : some value=input.val[chunk.val*16+byte.val]? := by
    rw [readFacts.2,←sourceAddress,List.getElem?_eq_getElem inputBound]
  rw [lowAddress,highAddress,inputByte]

#print axioms step_bytes
end AspisS1ValuesOwnedStepBytes
