import F3J_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QuerySource
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful installed query body actually executes its first squeeze and
advance, even when the decoder later selects an earlier state. -/
theorem first_pair {Hash : Type} (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (success : QueriesModel.queries B D before row payload=ok (.Ok out,after)) :
    ∃ absorbed block next,
      transcript.Transcript.absorb D before row payload=ok absorbed ∧
      D.digest absorbed.hash (TranscriptStep.readParts absorbed.state 1#u8)=ok block ∧
      D.digest absorbed.hash (TranscriptStep.readParts absorbed.state 2#u8)=ok next := by
  unfold QueriesModel.queries at success
  obtain ⟨absorbed,ha,success⟩ := bind_success _ _ _ success
  obtain ⟨s,h0,success⟩ := bind_success (lift (Array.to_slice absorbed.state)) _ _ success
  obtain ⟨s1,h1,success⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [1#u8]))) _ _ success
  obtain ⟨s2,h2,success⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [s,s1]))) _ _ success
  obtain ⟨block,hb,success⟩ := bind_success (D.digest absorbed.hash s2) _ _ success
  obtain ⟨pair,hi,success⟩ := bind_success _ _ _ success
  rcases pair with ⟨unused,put⟩
  obtain ⟨s3,h3,success⟩ := bind_success (lift (Array.to_slice absorbed.state)) _ _ success
  obtain ⟨s4,h4,success⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [2#u8]))) _ _ success
  obtain ⟨s5,h5,success⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [s3,s4]))) _ _ success
  obtain ⟨next,hn,success⟩ := bind_success (D.digest absorbed.hash s5) _ _ success
  cases Result.ok.inj h0
  cases Result.ok.inj h1
  cases Result.ok.inj h2
  cases Result.ok.inj h3
  cases Result.ok.inj h4
  cases Result.ok.inj h5
  exact ⟨absorbed,block,next,ha,hb,hn⟩

#print axioms first_pair
end AspisR1.F3J_QuerySource
end
