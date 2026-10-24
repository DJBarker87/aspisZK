import OraclePortPackedChoiceC4
import R1LiteralMatchingFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Parsed
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
abbrev FE := AspisWideTower.WideExact
attribute [local irreducible] CanonicalCutEnrichedTranscript.wordsFromMaps

theorem data_word (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (data : MatchingSupport.Data FE)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data) :
    data.V=(words parsed q).final := by
  obtain ⟨common,staged,row31,word,gamma,kappa,alpha0,alpha1,_,_,_,wordRead,_,_,_,_,dataEq⟩ :=
    LiteralMatchingFacts.read_success_components _ data read
  have wordEq : word=(words parsed q).final := by
    unfold LiteralTranscript.vAt typedRows at wordRead
    rw [List.getElem?_mapIdx] at wordRead
    cases entry : tr.rounds[30]? with
    | none => simp only [entry,Option.map_none,Option.bind_none,reduceCtorEq] at wordRead
    | some mc =>
      rcases mc with ⟨message,challenge⟩
      cases message with
      | initial root => simp [entry,restore] at wordRead
      | payload bytes =>
        simpa only [entry,Option.map_some,Option.bind_some,restore,
          show (30:Nat)≠2 by decide,if_false,ite_true,Option.some.injEq] using wordRead.symm
  rw [dataEq]
  exact wordEq

/-- The actual selected packed payload equals the global first-occurrence
map, including repeated parents across the checkpoint split. Authentication
is an existing indexed-Merkle boundary, not inferred from equal roots. -/
theorem packed_at (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos)) (j : Fin 22) :
    packed parsed q 2 (AspisR1.parentIndex (n:=65536) (q j)).val=
      some (slice (opening parsed j.val) 672 128) := by
  have agrees := OraclePortPackedChoiceC4.packed_agrees parsed q 2 recovered authenticated j.val j.isLt
  rw [authenticated j.val j.isLt] at agrees
  have idx : index q 2 j.val=(AspisR1.parentIndex (n:=65536) (q j)).val := by
    have jmod : (⟨j.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simp only [index,jmod,ite_true,AspisR1.parentIndex]
  simpa only [idx,OraclePortPackedChoiceC4.payload,show (2:Nat)≠0 by decide,
    show (2:Nat)≠1 by decide,if_false] using agrees

#print axioms data_word
#print axioms packed_at
end AspisR1.Port5Q1_Parsed
end
