import NGQ_QueryJoin
set_option autoImplicit false
namespace AspisR1.NGQ_TraceErase
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NGQ_QueryFactor

theorem read {α : Type} (a : Array α 22#usize) (i : Usize) (hi : i.val<22) :
    Array.index_usize a i=ok (a.val[i.val]'(by have := a.property; change a.val.length=22 at this; omega)) := by
  obtain ⟨v,call,value⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa only [Array.length,a.property,show (22#usize).val=22 by rfl] using hi))
  rw [value] at call
  exact call

/-- This erases evaluated diagnostic arguments only after proving totality.
The decoder reply, SAME selected state, and all 22 positions are preserved. -/
theorem finish_success (B : QueriesModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (blocks advances : Array (Array U8 32#usize) 8#usize)
    (q : Array U32 22#usize) (selected : Array U8 32#usize)
    (decode : B.decode blocks advances=ok (.Ok (q,selected)))
    (total : ∀ m, ∃ e, B.embed m=ok e) :
    finishQuery B D before blocks advances=ok (.Ok q,{before with state:=selected}) := by
  have h0 := read q 0#usize (by decide)
  have h1 := read q 1#usize (by decide)
  have h2 := read q 2#usize (by decide)
  have h3 := read q 3#usize (by decide)
  have h4 := read q 4#usize (by decide)
  have h5 := read q 5#usize (by decide)
  have h6 := read q 6#usize (by decide)
  have h7 := read q 7#usize (by decide)
  have h8 := read q 8#usize (by decide)
  have h9 := read q 9#usize (by decide)
  have h10 := read q 10#usize (by decide)
  have h11 := read q 11#usize (by decide)
  have h12 := read q 12#usize (by decide)
  have h13 := read q 13#usize (by decide)
  have h14 := read q 14#usize (by decide)
  have h15 := read q 15#usize (by decide)
  have h16 := read q 16#usize (by decide)
  have h17 := read q 17#usize (by decide)
  have h18 := read q 18#usize (by decide)
  have h19 := read q 19#usize (by decide)
  have h20 := read q 20#usize (by decide)
  have h21 := read q 21#usize (by decide)
  obtain ⟨v0,e0⟩ := total (q.val[0]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v1,e1⟩ := total (q.val[1]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v2,e2⟩ := total (q.val[2]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v3,e3⟩ := total (q.val[3]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v4,e4⟩ := total (q.val[4]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v5,e5⟩ := total (q.val[5]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v6,e6⟩ := total (q.val[6]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v7,e7⟩ := total (q.val[7]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v8,e8⟩ := total (q.val[8]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v9,e9⟩ := total (q.val[9]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v10,e10⟩ := total (q.val[10]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v11,e11⟩ := total (q.val[11]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v12,e12⟩ := total (q.val[12]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v13,e13⟩ := total (q.val[13]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v14,e14⟩ := total (q.val[14]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v15,e15⟩ := total (q.val[15]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v16,e16⟩ := total (q.val[16]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v17,e17⟩ := total (q.val[17]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v18,e18⟩ := total (q.val[18]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v19,e19⟩ := total (q.val[19]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v20,e20⟩ := total (q.val[20]'(by have := q.property; change q.val.length=22 at this; omega))
  obtain ⟨v21,e21⟩ := total (q.val[21]'(by have := q.property; change q.val.length=22 at this; omega))
  simp only [finishQuery,decode,core.result.Result.map_err,Port4C_GeometryStd.mapError,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  dsimp! only
  rw [h0,bind_tc_ok,e0,bind_tc_ok]
  dsimp! only
  rw [h1,bind_tc_ok,e1,bind_tc_ok]
  dsimp! only
  rw [h2,bind_tc_ok,e2,bind_tc_ok]
  dsimp! only
  rw [h3,bind_tc_ok,e3,bind_tc_ok]
  dsimp! only
  rw [h4,bind_tc_ok,e4,bind_tc_ok]
  dsimp! only
  rw [h5,bind_tc_ok,e5,bind_tc_ok]
  dsimp! only
  rw [h6,bind_tc_ok,e6,bind_tc_ok]
  dsimp! only
  rw [h7,bind_tc_ok,e7,bind_tc_ok]
  dsimp! only
  rw [h8,bind_tc_ok,e8,bind_tc_ok]
  dsimp! only
  rw [h9,bind_tc_ok,e9,bind_tc_ok]
  dsimp! only
  rw [h10,bind_tc_ok,e10,bind_tc_ok]
  dsimp! only
  rw [h11,bind_tc_ok,e11,bind_tc_ok]
  dsimp! only
  rw [h12,bind_tc_ok,e12,bind_tc_ok]
  dsimp! only
  rw [h13,bind_tc_ok,e13,bind_tc_ok]
  dsimp! only
  rw [h14,bind_tc_ok,e14,bind_tc_ok]
  dsimp! only
  rw [h15,bind_tc_ok,e15,bind_tc_ok]
  dsimp! only
  rw [h16,bind_tc_ok,e16,bind_tc_ok]
  dsimp! only
  rw [h17,bind_tc_ok,e17,bind_tc_ok]
  dsimp! only
  rw [h18,bind_tc_ok,e18,bind_tc_ok]
  dsimp! only
  rw [h19,bind_tc_ok,e19,bind_tc_ok]
  dsimp! only
  rw [h20,bind_tc_ok,e20,bind_tc_ok]
  dsimp! only
  rw [h21,bind_tc_ok,e21,bind_tc_ok]
  dsimp! only
  rfl


/-- Rejection retains the absorbed state and performs no diagnostic embedding. -/
theorem finish_rejected (B : QueriesModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (blocks advances : Array (Array U8 32#usize) 8#usize)
    (error : aspis_core.transcript.QuerySampleError)
    (decode : B.decode blocks advances=ok (.Err error)) :
    finishQuery B D before blocks advances=ok (.Err verifier.Error.Transcript,before) := by
  simp only [finishQuery,decode,core.result.Result.map_err,Port4C_GeometryStd.mapError,
    transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError,
    transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,bind_tc_ok]
  rfl
#print axioms read
#print axioms finish_success
#print axioms finish_rejected
end AspisR1.NGQ_TraceErase
