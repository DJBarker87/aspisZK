import NJO_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NJR_SuccessReads
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Stage2Finish

/-- A successful Horner traversal has actually read every coefficient in its
ordered index list; no field value or successful child is independently given. -/
theorem horner (bytes : Slice U8) (x a out : E) (indices : List Usize)
 (run : FIn_Polynomial.go bytes x indices a=ok out) :
 ∀ i∈indices,∃ c,FIn_Primitives.field bytes i=ok c := by
 induction indices generalizing a with
 | nil => intro i h;cases h
 | cons i rest ih =>
  unfold FIn_Polynomial.go at run
  obtain ⟨product,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨coefficient,field,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨next,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  intro j member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨coefficient,field⟩
  · exact ih next run j tail

theorem polynomial (bytes : Slice U8) (x out : E)
 (run : FIn_ExtractInstall.polynomial bytes x=ok out)
 (i : Usize) (inside : i.val<7) : ∃ c,FIn_Primitives.field bytes i=ok c := by
 rw [FIn_ExtractInstall.same] at run
 apply horner bytes x FIn_Polynomial.zero out _ run i
 simp only [List.mem_cons,List.not_mem_nil,or_false]
 have cases : i.val=6 ∨ i.val=5 ∨ i.val=4 ∨ i.val=3 ∨ i.val=2 ∨ i.val=1 ∨ i.val=0 := by omega
 rcases cases with h|h|h|h|h|h|h
 · exact Or.inl (UScalar.eq_of_val_eq h)
 · exact Or.inr (Or.inl (UScalar.eq_of_val_eq h))
 · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))
 · exact Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq h))))))

/-- Every successful round reaches the complete polynomial read sequence. -/
theorem round (r : NP6_StdModel.Reservation) (bytes : Slice U8) (x claim out : E)
 (number : Usize) (small : number.val≤1)
 (run : verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) bytes x claim number=ok (.Ok out)) :
 ∀ i : Usize,i.val<7→∃ c,FIn_Primitives.field bytes i=ok c := by
 have actual : Port4D_Round.round (IDa_Deployed.finish r) bytes x claim number=ok (.Ok out) := by
  rw [Port4D_Round.round_small _ _ _ _ _ small]
  exact run
 unfold Port4D_Round.round at actual
 simp only [IDa_Deployed.finish,bind_tc_ok,lift] at actual
 obtain ⟨c0,_,actual⟩:=Port3_PushFrame.bind_success _ _ _ actual
 obtain ⟨c4,_,actual⟩:=Port3_PushFrame.bind_success _ _ _ actual
 obtain ⟨lhs,_,actual⟩:=Port3_PushFrame.bind_success _ _ _ actual
 obtain ⟨rhs,_,actual⟩:=Port3_PushFrame.bind_success _ _ _ actual
 obtain ⟨different,_,actual⟩:=Port3_PushFrame.bind_success _ _ _ actual
 cases different with
 | true => cases actual
 | false =>
  obtain ⟨value,poly,_⟩:=Port3_PushFrame.bind_success _ _ _ actual
  intro i hi
  exact polynomial bytes x value poly i hi

/-- Full successful dot has read EVERY final-message field, using the existing
ordered source read trace. No field-input canonicality is an antecedent. -/
theorem dot (fm : Slice U8) (ws : Slice aspis_core.field.QM31) (out : E)
 (width : ws.val.length=64) (run : SAG_DotClosed.source fm ws=ok (.Ok out)) :
 ∀ i : Fin 64,∃ index value,index.val=i.val ∧
 AspisR1CurrentWide.Proof.finishField fm index=ok value := by
 obtain ⟨value,kernel,_⟩:=SAG_DotAdapter.sourceDot_success SAG_DotClosed.seed fm ws out run
 obtain ⟨n,indices,messages,weights,size,reads,_⟩:=SAG_DotIndexed.successful_finish_indexed_source_sum
  SAG_DotClosed.seed fm (SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws) value kernel
 have hlen : (SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws).len.val=64 := by
  change (ws.val.map SAG_DotAdapter.toFinishQ).length=64
  rw [List.length_map,width]
 have n64 : n=64 := size.trans hlen
 clear size
 subst n
 intro i
 exact ⟨indices i,messages i,(reads i).1,(reads i).2.2.1⟩

#print axioms horner
#print axioms polynomial
#print axioms round
#print axioms dot
end NJR_SuccessReads
