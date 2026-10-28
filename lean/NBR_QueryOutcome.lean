import NBR_QueryTotal
set_option autoImplicit false
namespace AspisR1.NBR_QueryOutcome
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBA_QueryDriver

theorem source {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (trace : NBL_QueryTrace.Trace D before row payload) :
    ∃ out, trace.result=ok out := by
  apply NBR_QueryTotal.walk trace.pairs.advances 7#usize trace.walk (by decide)
  intro pair member
  have index := (List.of_mem_zip member).2
  simp only [List.mem_cons,List.not_mem_nil,or_false] at index
  rcases index with h|h|h|h|h|h|h|h <;> rw [h] <;> decide

#print axioms source
end AspisR1.NBR_QueryOutcome
