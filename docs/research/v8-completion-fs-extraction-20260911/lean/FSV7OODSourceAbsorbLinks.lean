import FSV7OODAbsorbLink
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7OODSourceAbsorbLinks
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
open FSV7OODSampler FSV8OODBodyScript FSV7OODBodyScript
open FSV7OODAbsorbLink FSExposureOrder

abbrev Bytes := List UInt8
abbrev HashBlock := FSBoundedTranscript.Block
abbrev HashTape := FSBoundedTranscript.Tape
abbrev HashOracle := FSBoundedTranscript.Oracle
abbrev Point := FSV7OODBodyScript.Point
abbrev Result := FSV7OODBodyScript.Result
noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/- The two label-62 records are extracted from the successful concrete
   execution itself.  The existential answers are the actual query replies,
   not sampled or independently supplied values. -/
theorem successful_source_absorb_links {n m : Nat}
    (firstWork : Point → Script Bytes HashBlock Unit n)
    (secondWork : Point → Point → Script Bytes HashBlock Unit m)
    (body : Bytes) (digest : HashBlock) (tape : HashTape)
    (out : Result) (finalDigest : HashBlock)
    (success :
      (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
      FSFirstFresh.empty).1 = some (Except.ok out, finalDigest)) :
    ∃ firstState firstAnswer secondState secondAnswer,
      LinkedAbsorb
        (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
          FSFirstFresh.empty).2.log
        (absorbInput firstState 62 (0 :: FSV8OODBodyScript.answerBytes body 0)) firstAnswer ∧
      LinkedAbsorb
        (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
          FSFirstFresh.empty).2.log
        (absorbInput secondState 62 (1 :: FSV8OODBodyScript.answerBytes body 1)) secondAnswer := by
  have canonical := FSV8OODBodyScript.checked_success_canonical decodePoint
    firstWork secondWork body digest tape FSFirstFresh.empty (.ok out, finalDigest) success
  simp only [FSV7OODBodyScript.sourceScript, FSV8OODBodyScript.checkedBodyPairScript,
    if_pos canonical] at success ⊢
  unfold FSV8OODBodyScript.bodyPairScript at success ⊢
  ·
    rw [run_bind] at success ⊢
    have firstExact := run_circle decodePoint tape 3
      { digest := digest, oracle := FSFirstFresh.empty }
    change run tape (circleScript decodePoint 3 digest) FSFirstFresh.empty = _ at firstExact
    rw [firstExact] at success ⊢
    cases hfirst : (circle decodePoint tape 3
        { digest := digest, oracle := FSFirstFresh.empty }).1 with
    | error e => simp only [hfirst, run] at success; cases success
    | ok firstPoint =>
      simp only [hfirst] at success
      rw [run_bind, run_answerScript] at success ⊢
      cases hfirstWork : (run tape (firstWork firstPoint)
          (circle decodePoint tape 3 { digest := digest, oracle := FSFirstFresh.empty }).2.oracle).1 with
      | none => simp only [hfirstWork, Option.map_none] at success; cases success
      | some firstUnit =>
        simp only [hfirstWork, Option.map_some] at success
        rw [run_bind] at success ⊢
        let firstState : HashBlock :=
          (circle decodePoint tape 3 { digest := digest, oracle := FSFirstFresh.empty }).2.digest
        let firstOracle : HashOracle :=
          (run tape (firstWork firstPoint)
            (circle decodePoint tape 3 { digest := digest, oracle := FSFirstFresh.empty }).2.oracle).2
        let firstData : Bytes := 0 :: answerBytes body 0
        have firstLinked := absorb_linked_after tape firstState 62 firstData
          (fun afterFirst => bind (distinctScript decodePoint firstPoint 3 afterFirst)
            (fun secondDraw => afterSecond firstPoint
              afterFirst secondWork body secondDraw)) firstOracle
          (absorb tape ⟨firstState, firstOracle⟩ 62 firstData).digest (by rfl)
        rw [run_absorb tape ⟨firstState, firstOracle⟩ 62 firstData] at success ⊢
        simp only [] at success
        rw [run_bind, run_distinct] at success ⊢
        let afterFirst := absorb tape ⟨firstState, firstOracle⟩ 62 firstData
        cases hsecond : (distinct decodePoint firstPoint tape 3 afterFirst).1 with
        | error e => dsimp [afterFirst] at hsecond; simp only [hsecond, afterSecond, run] at success; cases success
        | ok secondPoint =>
          dsimp [afterFirst] at hsecond
          simp only [hsecond, afterSecond] at success
          rw [run_bind, run_answerScript] at success ⊢
          cases hsecondWork : (run tape (secondWork firstPoint secondPoint)
              (distinct decodePoint firstPoint tape 3 afterFirst).2.oracle).1 with
          | none => dsimp [afterFirst] at hsecondWork; simp only [hsecondWork, Option.map_none] at success; cases success
          | some secondUnit =>
            dsimp [afterFirst] at hsecondWork
            simp only [hsecondWork, Option.map_some] at success
            rw [run_bind] at success ⊢
            let secondState : HashBlock :=
              (distinct decodePoint firstPoint tape 3 afterFirst).2.digest
            let secondOracle : HashOracle :=
              (run tape (secondWork firstPoint secondPoint)
                (distinct decodePoint firstPoint tape 3 afterFirst).2.oracle).2
            let secondData : Bytes := 1 :: answerBytes body 1
            have secondLinked := absorb_linked_after tape secondState 62 secondData
              (fun _ => (.done
                ((Except.ok ({
                    first := firstPoint
                    second := secondPoint
                    afterFirstAnswer :=
                      (absorb tape ⟨firstState, firstOracle⟩ 62 firstData).digest
                    afterSecondAnswer :=
                      (absorb tape ⟨secondState, secondOracle⟩ 62 secondData).digest
                  } : Result) : Except Error Result),
                  (absorb tape ⟨secondState, secondOracle⟩ 62 secondData).digest) :
                Script Bytes HashBlock (Except Error Result × HashBlock) 0))
              secondOracle (absorb tape ⟨secondState, secondOracle⟩ 62 secondData).digest (by rfl)
            rw [run_absorb tape ⟨secondState, secondOracle⟩ 62 secondData] at success ⊢
            simp only [run] at success
            cases success
            refine ⟨firstState, (absorb tape ⟨firstState, firstOracle⟩ 62 firstData).digest,
              secondState, (absorb tape ⟨secondState, secondOracle⟩ 62 secondData).digest, ?_, ?_⟩
            · exact firstLinked
            · exact secondLinked
#print axioms successful_source_absorb_links
end
end AspisV8Completion.FSV7OODSourceAbsorbLinks
