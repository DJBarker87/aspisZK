import S1ValuesOwnedExpansionBytesV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedReferenceBytes
open Aeneas Aeneas.Std Result WP AspisS1ValuesOwned
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

/-- Every accepted codec success derives its own dimensions and exact byte
formula from the same complete source call. No loop or alignment premise. -/
theorem reference_bytes (input original next updated : Buffer)
    (call : values_owned_reference input original=ok (.Ok (),next,updated)) :
    next=input ∧ updated.length=original.length ∧
      original.length=2*input.length ∧ input.length%16=0 ∧
      ∀ j, j<updated.length → updated.val[j]?=Desired input j := by
  unfold values_owned_reference at call
  obtain ⟨rem,hrem,call⟩ := bind_success _ _ _ call
  split at call
  · cases call
  · rename_i aligned
    obtain ⟨twice,htwice,call⟩ := bind_success _ _ _ call
    split at call
    · cases call
    · rename_i shape
      obtain ⟨count,hcount,call⟩ := bind_success _ _ _ call
      obtain ⟨ni,no,hloop,call⟩ := pair_success _ _ _ call
      have same := Result.ok.inj call
      have sn : ni=next := congrArg (fun p => p.2.1) same
      have so : no=updated := congrArg (fun p => p.2.2) same
      subst ni
      subst no
      have hs : (alloc.vec.Vec.len input % 16#usize) ⦃ r => r.val=input.length%16 ⦄ := by
        apply UScalar.rem_spec
        scalar_tac
      obtain ⟨rem1,remCall,remValue⟩ := spec_imp_exists hs
      have sr : rem1=rem := Result.ok.inj (remCall.symm.trans hrem)
      subst rem1
      have remZero : rem=0#usize := by scalar_tac
      have alignment : input.length%16=0 := by scalar_tac
      have twiceValue := AspisS1FrameArithmetic.mul_value 2#usize (alloc.vec.Vec.len input) twice htwice
      have outputShape : original.length=2*input.length := by scalar_tac
      obtain ⟨count1,countCall,countValue⟩ := UScalar.div_spec (alloc.vec.Vec.len input)
        (y:=16#usize) (by scalar_tac)
      have sc : count1=count := Result.ok.inj (countCall.symm.trans hcount)
      subst count1
      have inputRange : count.val*16 ≤ input.length := by scalar_tac
      have outputRange : count.val*32 ≤ original.length := by scalar_tac
      have exactSize : count.val*32=original.length := by scalar_tac
      obtain ⟨inputKept,lengthKept,bytes⟩ :=
        AspisS1ValuesOwnedExpansionBytes.loop_bytes input original next updated count inputRange outputRange hloop
      refine ⟨inputKept,lengthKept,outputShape,alignment,?_⟩
      intro j bound
      have completed : j<count.val*32 := by omega
      simpa only [if_pos completed] using bytes j

#print axioms reference_bytes
end AspisS1ValuesOwnedReferenceBytes
