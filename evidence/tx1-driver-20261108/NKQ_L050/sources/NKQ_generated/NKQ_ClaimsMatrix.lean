import NKQ_DecodeCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_ClaimsMatrix
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish AspisR1ClaimsUnrolledParent

def ParentCanon (c : Claims) : Prop := ∀ row∈c.val,NKQ_DecodeCanonical.ParentRowCanon row

theorem rows (record : Record) (out : Claims)
 (call : decodeRows NJT_ClaimsRef_Value.external record=ok (.Ok out)) :
 ∃ a b c,sourceDecode 29#usize record 0#usize=ok (.Ok a) ∧
 sourceDecode 29#usize record 29#usize=ok (.Ok b) ∧
 sourceDecode 29#usize record 58#usize=ok (.Ok c) ∧ out=⟨[a,b,c],by simp⟩ := by
 simp only [decodeRows,NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external] at call
 cases d0 : sourceDecode 29#usize record 0#usize with
 | fail error => simp [d0] at call
 | div => simp [d0] at call
 | ok r0 =>
  cases r0 with
  | Err error => simp [d0] at call
  | Ok a =>
   cases d1 : sourceDecode 29#usize record 29#usize with
   | fail error => simp [d0,d1] at call
   | div => simp [d0,d1] at call
   | ok r1 =>
    cases r1 with
    | Err error => simp [d0,d1] at call
    | Ok b =>
     cases d2 : sourceDecode 29#usize record 58#usize with
     | fail error => simp [d0,d1,d2] at call
     | div => simp [d0,d1,d2] at call
     | ok r2 =>
      cases r2 with
      | Err error => simp [d0,d1,d2] at call
      | Ok c =>
       have same : (⟨[a,b,c],by simp⟩ : Claims)=out :=
        core.result.Result.Ok.inj (Result.ok.inj (by simpa only [d0,d1,d2,bind_tc_ok] using call))
       exact ⟨a,b,c,d0,d1,d2,same.symm⟩

theorem canonical (record : Record) (out : Claims)
 (call : decodeRows NJT_ClaimsRef_Value.external record=ok (.Ok out)) : ParentCanon out := by
 obtain ⟨a,b,c,da,db,dc,same⟩:=rows record out call
 rw [same]
 intro row member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl
 · exact NKQ_DecodeCanonical.parent record 0#usize a da
 · exact NKQ_DecodeCanonical.parent record 29#usize b db
 · exact NKQ_DecodeCanonical.parent record 58#usize c dc

/-- Fixed safe reference, all three SAME calls. No decoder or successful
allocation is introduced as a caller assumption. -/
theorem reference (pre : r1_wire.Prefix) (out : Claims)
 (call : NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref pre)=ok (.Ok out)) : ParentCanon out := by
 rw [NJT_ClaimsRef_Value.reference] at call
 unfold NJT_ClaimsRef_Value.decode at call
 cases getter : sourceRecord pre 25#u8 with
 | fail error => simp [getter] at call
 | div => simp [getter] at call
 | ok reply =>
  cases reply with
  | Err error => simp [getter] at call
  | Ok record =>
   have decoded : decodeRows NJT_ClaimsRef_Value.external record=ok (.Ok out) := by
    simpa only [getter,bind_tc_ok] using call
   exact canonical record out decoded
#print axioms rows
#print axioms canonical
#print axioms reference
end AspisR1.NKQ_ClaimsMatrix
end
