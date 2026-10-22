import CheckpointBytes4Ops

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4SemanticFields
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Sections CheckpointBytes4Ops

private theorem cons_success (read : ReadK) (n : Nat) (r next last : verifier.Reader)
    (x : K) (xs : List K)
    (first : read r = ok (.Ok x,next))
    (tail : readList read n next = ok (.Ok (xs,last))) :
    readList read (n+1) r = ok (.Ok (x::xs,last)) := by
  rw [readList,first]
  change (do
    let rest ← readList read n next
    match rest with
    | .Err e => ok (core.result.Result.Err e)
    | .Ok (ys,finish) => ok (core.result.Result.Ok (x::ys,finish))) = _
  rw [tail]
  rfl

/-- Every output of the source's ten unrolled reads comes from the matching
ordered sequential decoder, with the exact final cursor. -/
theorem semantic_fields (read : ReadK) (bytes : Slice U8) (start finish : Usize)
    (values : Array K 10#usize)
    (success : semanticUsing read bytes start = ok (.Ok (values,finish))) :
    ∃ last : verifier.Reader,
      readList read 10 ⟨bytes,start⟩ = ok (.Ok (values.val,last)) ∧ last.at = finish := by
  unfold semanticUsing at success
  simp only [withK] at success
  obtain ⟨⟨value0,r1⟩,read0,tail0⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  cases value0 with
  | Err e => cases tail0
  | Ok x0 =>
    obtain ⟨⟨value1,r2⟩,read1,tail1⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail0
    cases value1 with
    | Err e => cases tail1
    | Ok x1 =>
      obtain ⟨⟨value2,r3⟩,read2,tail2⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail1
      cases value2 with
      | Err e => cases tail2
      | Ok x2 =>
        obtain ⟨⟨value3,r4⟩,read3,tail3⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail2
        cases value3 with
        | Err e => cases tail3
        | Ok x3 =>
          obtain ⟨⟨value4,r5⟩,read4,tail4⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail3
          cases value4 with
          | Err e => cases tail4
          | Ok x4 =>
            obtain ⟨⟨value5,r6⟩,read5,tail5⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail4
            cases value5 with
            | Err e => cases tail5
            | Ok x5 =>
              obtain ⟨⟨value6,r7⟩,read6,tail6⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail5
              cases value6 with
              | Err e => cases tail6
              | Ok x6 =>
                obtain ⟨⟨value7,r8⟩,read7,tail7⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail6
                cases value7 with
                | Err e => cases tail7
                | Ok x7 =>
                  obtain ⟨⟨value8,r9⟩,read8,tail8⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail7
                  cases value8 with
                  | Err e => cases tail8
                  | Ok x8 =>
                    obtain ⟨⟨value9,r10⟩,read9,tail9⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail8
                    cases value9 with
                    | Err e => cases tail9
                    | Ok x9 =>
                      have eq := core.result.Result.Ok.inj (Result.ok.inj tail9)
                      have hv := congrArg Prod.fst eq
                      have hc := congrArg Prod.snd eq
                      dsimp only at hv hc
                      subst values finish
                      refine ⟨r10,?_,rfl⟩
                      change readList read 10 ⟨bytes,start⟩ = ok (.Ok ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9],r10))
                      exact cons_success read 9 _ _ _ _ _ read0 (cons_success read 8 _ _ _ _ _ read1 (cons_success read 7 _ _ _ _ _ read2 (cons_success read 6 _ _ _ _ _ read3 (cons_success read 5 _ _ _ _ _ read4 (cons_success read 4 _ _ _ _ _ read5 (cons_success read 3 _ _ _ _ _ read6 (cons_success read 2 _ _ _ _ _ read7 (cons_success read 1 _ _ _ _ _ read8 (cons_success read 0 _ _ _ _ _ read9 (rfl))))))))))

/-- The C5 scalar reader is consumed on the real section, rather than an
assumed equality of semantic output arrays. -/
theorem semantic_c5_fields (bytes : Slice U8) (start finish : Usize)
    (values : Array K 10#usize)
    (success : readSemanticAlpha bytes start = ok (.Ok (values,finish))) :
    ∃ last : verifier.Reader,
      readList c5ReadK 10 ⟨bytes,start⟩ = ok (.Ok (values.val,last)) ∧ last.at = finish := by
  obtain ⟨last,run,cursor⟩ := semantic_fields CheckpointBytes3Reader.readK bytes start finish values success
  rw [read_list_identification] at run
  exact ⟨last,run,cursor⟩

#print axioms cons_success
#print axioms semantic_fields
#print axioms semantic_c5_fields
end AspisR1.CheckpointBytes4SemanticFields
end
