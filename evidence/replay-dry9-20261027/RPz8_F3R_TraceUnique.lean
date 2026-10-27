import RPz8_F3R_TraceHead
import RPz8_F3J_ValidatedLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_TraceUnique
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem unique {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {before after after' : r1_wire.SemanticTranscript H}
    {cs ds : List (SourceFull25.Call D pre)}
    (left : SourceFull25.Trace D pre before after cs)
    (right : SourceFull25.Trace D pre before after' ds)
    (rows : cs.map (fun c=>c.row.val)=ds.map (fun c=>c.row.val))
    (below : ∀ c∈cs,c.row.val<25) :
    after=after' ∧ sourceLog cs=sourceLog ds := by
  induction left generalizing ds after' with
  | nil self =>
    have empty : ds=[] := by
      have h := congrArg List.length rows
      simp only [List.length_map,List.length_nil] at h
      exact List.length_eq_zero_iff.mp h.symm
    subst ds
    cases right
    exact ⟨rfl,rfl⟩
  | @cons after cs c tail ih =>
    cases ds with
    | nil=>cases rows
    | cons d ds=>
      obtain ⟨beforeEq,tail'⟩ := F3R_TraceHead.head d ds right
      have rowEq : c.row=d.row := UScalar.eq_of_val_eq (List.cons.inj rows).1
      have read := c.validated
      rw [rowEq] at read
      have records : c.record=d.record := core.result.Result.Ok.inj (Result.ok.inj (read.symm.trans d.validated))
      have ret := c.semantic
      rw [beforeEq,records] at ret
      have state : c.after=d.after := congrArg Prod.snd (Result.ok.inj (ret.symm.trans d.semantic))
      rw [← state] at tail'
      have next := ih tail' (List.cons.inj rows).2 (fun x hx=>below x (List.mem_cons_of_mem c hx))
      refine ⟨next.1,?_⟩
      have cb := below c List.mem_cons_self
      have db : d.row.val<25 := by rw [← rowEq];exact cb
      have logEq : callLog c=callLog d := by
        rw [← F3J_ValidatedLog.semantic c cb,← F3J_ValidatedLog.semantic d db,beforeEq,records]
      simp only [sourceLog,List.flatMap_cons]
      exact congrArg₂ List.append logEq next.2

#print axioms unique
end AspisR1.F3R_TraceUnique
end
