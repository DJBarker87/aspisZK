import S2TrustedSdkBorrow
set_option autoImplicit false
namespace NHJ_SdkBracket
open AspisR1.S2Trust

theorem filter_fresh (guards : List Guard) (token : Nat)
    (fresh : guards.find? (fun g => g.token == token) = none) :
    guards.filter (fun g => g.token != token) = guards := by
  induction guards with
  | nil => rfl
  | cons g guards ih =>
    by_cases same : g.token = token
    · simp [List.find?_cons,same] at fresh
    · have rest : guards.find? (fun g => g.token == token) = none := by
        simpa [List.find?_cons,same] using fresh
      simp [same,ih rest]

/-- Any existing shared guards and external counts are preserved. No zero-counter
or empty-guard premise is used. This is the returning shared bracket only. -/
theorem shared_release {F : Type} (s : Heap F) (account token owner : Nat)
    (fresh : lookup s token = none) :
    release (acquire s (s.accounts account).1 token owner .shared)
      ⟨token,(s.accounts account).1,owner,.shared,(s.payload (s.accounts account).1).descriptor⟩ = s := by
  have keep := filter_fresh s.guards token fresh
  have counters :
      put (put s.counter (s.accounts account).1 (s.counter (s.accounts account).1 + 1))
        (s.accounts account).1
        (put s.counter (s.accounts account).1 (s.counter (s.accounts account).1 + 1)
          (s.accounts account).1 - 1) = s.counter := by
    funext cell
    by_cases same : cell = (s.accounts account).1 <;> simp [put,same]
  simpa [release,acquire,keep,counters]


/-- The returning owned-copy allocation may change ambient allocator state,
which comes from that same cut; it cannot alter SDK cells or the live guard. -/
theorem shared_release_ambient {F : Type} (s : Heap F) (account token owner : Nat)
    (fresh : lookup s token = none) (afterAllocation : F) :
    release ({acquire s (s.accounts account).1 token owner .shared with
      ambient := afterAllocation})
      ⟨token,(s.accounts account).1,owner,.shared,(s.payload (s.accounts account).1).descriptor⟩ =
      {s with ambient := afterAllocation} := by
  change {release (acquire s (s.accounts account).1 token owner .shared)
      ⟨token,(s.accounts account).1,owner,.shared,(s.payload (s.accounts account).1).descriptor⟩
      with ambient := afterAllocation} = _
  rw [shared_release s account token owner fresh]
#print axioms filter_fresh
#print axioms shared_release
#print axioms shared_release_ambient
end NHJ_SdkBracket
