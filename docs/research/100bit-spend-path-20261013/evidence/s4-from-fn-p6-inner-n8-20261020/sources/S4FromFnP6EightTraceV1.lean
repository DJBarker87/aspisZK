import S4FourDotsP6ArrayOperationV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

theorem statefulFromFnTrace_eight_calls {T F : Type}
    (step : (F × Usize) → Nat → Result (T × (F × Usize)))
    (initial : F × Usize)
    (count : Nat) (hcount : count = 8)
    {values : List T} {final : F × Usize}
    (htrace : AspisR1FromFnP6.StatefulFromFnTrace step count 0
      initial values final) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 s1 s2 s3 s4 s5 s6 s7 s8,
      values = [v0, v1, v2, v3, v4, v5, v6, v7] ∧
      step initial 0 = .ok (v0, s1) ∧
      step s1 1 = .ok (v1, s2) ∧
      step s2 2 = .ok (v2, s3) ∧
      step s3 3 = .ok (v3, s4) ∧
      step s4 4 = .ok (v4, s5) ∧
      step s5 5 = .ok (v5, s6) ∧
      step s6 6 = .ok (v6, s7) ∧
      step s7 7 = .ok (v7, s8) ∧
      final = s8 := by
  cases hcount
  cases htrace with
  | @call _ _ _ s1 final v0 vs0 h0 t0 =>
    cases t0 with
    | @call _ _ _ s2 final v1 vs1 h1 t1 =>
      cases t1 with
      | @call _ _ _ s3 final v2 vs2 h2 t2 =>
        cases t2 with
        | @call _ _ _ s4 final v3 vs3 h3 t3 =>
          cases t3 with
          | @call _ _ _ s5 final v4 vs4 h4 t4 =>
            cases t4 with
            | @call _ _ _ s6 final v5 vs5 h5 t5 =>
              cases t5 with
              | @call _ _ _ s7 final v6 vs6 h6 t6 =>
                cases t6 with
                | @call _ _ _ s8 final v7 vs7 h7 t7 =>
                  cases t7 with
                  | done _ _ =>
                    refine ⟨v0,v1,v2,v3,v4,v5,v6,v7,s1,s2,s3,s4,s5,s6,s7,final,?_,h0,?_,?_,?_,?_,?_,?_,?_,rfl⟩
                    · rfl
                    · simpa only [Nat.zero_add] using h1
                    · simpa only [Nat.zero_add,Nat.add_assoc] using h2
                    · simpa only [Nat.zero_add,Nat.add_assoc] using h3
                    · simpa only [Nat.zero_add,Nat.add_assoc] using h4
                    · simpa only [Nat.zero_add,Nat.add_assoc] using h5
                    · simpa only [Nat.zero_add,Nat.add_assoc] using h6
                    · simpa only [Nat.zero_add,Nat.add_assoc] using h7


theorem arrayFromFnP6_success_eight_calls {T F : Type}
    (N : Usize) (hN : N.val = 8)
    (callback : core.ops.function.FnMut F Usize T) (initial : F)
    {values : Aeneas.Std.Array T N}
    (h : arrayFromFnP6 N callback initial = .ok values) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 s1 s2 s3 s4 s5 s6 s7 s8,
      values.val = [v0, v1, v2, v3, v4, v5, v6, v7] ∧
      fnMutStep callback (initial, 0#usize) 0 = .ok (v0, s1) ∧
      fnMutStep callback s1 1 = .ok (v1, s2) ∧
      fnMutStep callback s2 2 = .ok (v2, s3) ∧
      fnMutStep callback s3 3 = .ok (v3, s4) ∧
      fnMutStep callback s4 4 = .ok (v4, s5) ∧
      fnMutStep callback s5 5 = .ok (v5, s6) ∧
      fnMutStep callback s6 6 = .ok (v6, s7) ∧
      fnMutStep callback s7 7 = .ok (v7, s8) := by
  obtain ⟨final, htrace⟩ := arrayFromFnP6_success_trace N callback initial h
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,s1,s2,s3,s4,s5,s6,s7,s8,hvals,h0,h1,h2,h3,h4,h5,h6,h7,_⟩ :=
    statefulFromFnTrace_eight_calls (fnMutStep callback) (initial,0#usize) N.val hN htrace
  exact ⟨v0,v1,v2,v3,v4,v5,v6,v7,s1,s2,s3,s4,s5,s6,s7,s8,hvals,h0,h1,h2,h3,h4,h5,h6,h7⟩

#print axioms statefulFromFnTrace_eight_calls
#print axioms arrayFromFnP6_success_eight_calls

end AspisR1FromFnP6Generated
