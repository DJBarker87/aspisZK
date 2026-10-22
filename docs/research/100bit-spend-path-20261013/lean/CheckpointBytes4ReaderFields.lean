import CheckpointBytes4Sections

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4ReaderFields
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes3Reader
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
open MultiproofConeCanonical

def sourceK (x : OraclePortCheckpointAbiC5.K) : aspis_core.field.QM31 :=
  CheckpointBytes3Namespaces.fromK (CheckpointBytes3KDecode.rawK x)
def sourceE (x : OraclePortCheckpointAbiC5.E) : aspis_core.field.wide_exact.WideExact :=
  CheckpointBytes3Namespaces.fromE (CheckpointBytes3EDecode.rawE x)

/-- Every successful source-shaped K reader identifies its exact flat C5
slice, decoded value, unchanged backing and advanced cursor. -/
theorem k_success (r out : verifier.Reader) (q : aspis_core.field.QM31)
    (bound : r.at.val+16 ≤ r.bytes.val.length)
    (success : readK r = ok (.Ok q,out)) :
    ∃ x, ExactLeafFieldCodec.decodeQM31 (slice (bytesOf r.bytes.val) r.at.val 16) = some x ∧
      sourceK x = q ∧ out.at.val = r.at.val+16 ∧ out.bytes = r.bytes := by
  obtain ⟨b,last,contents,cursor,backing,run⟩ := read_k_c5 r bound
  rw [run] at success
  cases decoded : ExactLeafFieldCodec.decodeQM31 (bytesOf b.val) with
  | none => simp only [decoded,Option.map_none,optionK] at success; cases success
  | some x =>
    rw [decoded] at success
    have eq := Result.ok.inj success
    have valueEq := congrArg Prod.fst eq
    have readerEq := congrArg Prod.snd eq
    change core.result.Result.Ok (sourceK x) = .Ok q at valueEq
    have valueEq := core.result.Result.Ok.inj valueEq
    dsimp only at readerEq
    subst out
    refine ⟨x,?_,valueEq,cursor,backing⟩
    simpa only [OraclePortCompactDraft.slice,bytesOf,List.map_drop,List.map_take,contents] using decoded

/-- The analogous exact-width E reader, including both wide halves. -/
theorem e_success (r out : verifier.Reader) (q : aspis_core.field.wide_exact.WideExact)
    (bound : r.at.val+32 ≤ r.bytes.val.length)
    (success : readE r = ok (.Ok q,out)) :
    ∃ x, FoldedLeafCodec.decodeWide (slice (bytesOf r.bytes.val) r.at.val 32) = some x ∧
      sourceE x = q ∧ out.at.val = r.at.val+32 ∧ out.bytes = r.bytes := by
  obtain ⟨b,last,contents,cursor,backing,run⟩ := read_e_c5 r bound
  rw [run] at success
  cases decoded : FoldedLeafCodec.decodeWide (bytesOf b.val) with
  | none => simp only [decoded,Option.map_none,optionE] at success; cases success
  | some x =>
    rw [decoded] at success
    have eq := Result.ok.inj success
    have valueEq := congrArg Prod.fst eq
    have readerEq := congrArg Prod.snd eq
    change core.result.Result.Ok (sourceE x) = .Ok q at valueEq
    have valueEq := core.result.Result.Ok.inj valueEq
    dsimp only at readerEq
    subst out
    refine ⟨x,?_,valueEq,cursor,backing⟩
    simpa only [OraclePortCompactDraft.slice,bytesOf,List.map_drop,List.map_take,contents] using decoded

#print axioms k_success
#print axioms e_success
end AspisR1.CheckpointBytes4ReaderFields
end
