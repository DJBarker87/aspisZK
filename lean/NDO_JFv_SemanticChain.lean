import NDO_JFv_OracleTotal
set_option autoImplicit false
namespace AspisR1.JFv_SemanticChain
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem success {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (pre : r1_wire.Prefix) (rows : List U8) (start : Nat)
    (t : r1_wire.SemanticTranscript H) (initial : t.next_row.val=start)
    (order : rows.map UScalar.val=List.range' start rows.length) (bound : start+rows.length≤25) :
    ∃ after qs,BeginCalls.SemanticRun D pre rows t after qs ∧
      (∀ q ∈ qs,JFv_RoundArithmetic.Canonical q) := by
  induction rows generalizing start t with
  | nil => exact ⟨t,[],.nil t,by simp⟩
  | cons row rows ih =>
    have ordered : row.val=start ∧ rows.map UScalar.val=List.range' (start+1) rows.length := by
      simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using order
    have same : row=t.next_row := UScalar.eq_of_val_eq (ordered.1.trans initial.symm)
    obtain ⟨vr,q,mid,record,rowEq,call,next,canon⟩ := JFv_PrefixCall.success D total pre t row same
      (by simp only [List.length_cons] at bound;omega)
    obtain ⟨after,qs,tail,canonical⟩ := ih (start+1) mid (by omega) ordered.2
      (by simp only [List.length_cons] at bound;omega)
    refine ⟨after,q::qs,.cons record call tail,?_⟩
    intro value member
    rcases List.mem_cons.mp member with equal | member
    · subst value;exact canon
    · exact canonical value member

#print axioms success
end AspisR1.JFv_SemanticChain
