import Aeneas
open Aeneas Aeneas.Std Result
namespace AspisR1.QueryValidatorGateInversion

theorem false_of_gate {ε : Type} (err : ε) (r : Result Bool)
    (h : (do let b ← r; if b then ok (core.result.Result.Err err) else ok (core.result.Result.Ok ()))
      = ok (core.result.Result.Ok ())) : r = ok false := by
  cases r <;> simp_all

theorem two_false_of_gates {ε : Type} (err : ε)
    (r0 r1 : Result Bool)
    (h : (do
      let b0 ← r0
      if b0 then ok (core.result.Result.Err err) else do
        let b1 ← r1
        if b1 then ok (core.result.Result.Err err) else
            ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ())) :
      r0 = ok false ∧ r1 = ok false := by
  cases r0 with
  | ok b0 =>
    cases b0
    · have h1 : (do let b1 ← r1; if b1 then ok (core.result.Result.Err err) else ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
        simpa using h
      exact ⟨rfl, false_of_gate err r1 h1⟩
    · simp at h
  | fail e => simp at h
  | div => simp at h

theorem three_false_of_gates {ε : Type} (err : ε)
    (r0 r1 r2 : Result Bool)
    (h : (do
      let b0 ← r0
      if b0 then ok (core.result.Result.Err err) else do
        let b1 ← r1
        if b1 then ok (core.result.Result.Err err) else do
          let b2 ← r2
          if b2 then ok (core.result.Result.Err err) else
            ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ())) :
      r0 = ok false ∧ r1 = ok false ∧ r2 = ok false := by
  cases r0 with
  | ok b0 =>
    cases b0
    · have hrest : (do
        let b1 ← r1
        if b1 then ok (core.result.Result.Err err) else do
          let b2 ← r2
          if b2 then ok (core.result.Result.Err err) else ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
        simpa using h
      obtain ⟨h1, h2⟩ := two_false_of_gates err r1 r2 hrest
      exact ⟨rfl, h1, h2⟩
    · simp at h
  | fail e => simp at h
  | div => simp at h

#print axioms false_of_gate
#print axioms two_false_of_gates
#print axioms three_false_of_gates
end AspisR1.QueryValidatorGateInversion
