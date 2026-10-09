import FSOODSampler
set_option autoImplicit false

namespace AspisV8Completion.FSOODSamplerExposure
open FSOracleExecution FSBoundedTranscript FSExposureOrder FSTranscriptScript
open AspisV8Completion.FSOODSampler
variable {Point : Type}

/-- A chronological oracle prefix preserves every already logged input. -/
theorem mem_inputs_of_prefix {a b : Oracle} {input : Bytes}
    (h : Prefix a b) (seen : input ∈ inputs a.log) : input ∈ inputs b.log := by
  obtain ⟨tail, ht⟩ := h
  rw [ht]
  simp only [inputs, List.map_append]
  exact List.mem_append_left _ seen

private theorem query_logs_input (tape : Tape) (s : Oracle) (input : Bytes) :
    input ∈ inputs (query tape s input).2.log := by
  obtain ⟨event, heq, hin, _⟩ := query_log tape s input
  rw [heq]
  simp only [inputs, List.map_append]
  exact List.mem_append_right _ (by simpa [hin])

theorem squeeze_logs_start (tape : Tape) (s : Transcript) :
    squeezeInput s.digest ∈ inputs (squeeze tape s).2.oracle.log := by
  let out := query tape s.oracle (List.ofFn s.digest ++ [1])
  have hfirst : squeezeInput s.digest ∈ inputs out.2.log := by
    change (List.ofFn s.digest ++ [1]) ∈ inputs out.2.log
    exact query_logs_input tape s.oracle (List.ofFn s.digest ++ [1])
  exact mem_inputs_of_prefix (query_prefix tape out.2 (List.ofFn s.digest ++ [2])) hfirst

private theorem challenge_prefix_from_squeeze (tape : Tape) (s : Transcript) :
    Prefix (squeeze tape s).2.oracle (challenge tape s).2.oracle := by
  exact limbs_prefix tape 4 ⟨(squeeze tape s).2, words (squeeze tape s).1⟩

theorem challenge_logs_start (tape : Tape) (s : Transcript) :
    squeezeInput s.digest ∈ inputs (challenge tape s).2.oracle.log := by
  exact mem_inputs_of_prefix (challenge_prefix_from_squeeze tape s)
    (squeeze_logs_start tape s)

theorem circle_prefix (decode : List Nat → Option Point) (tape : Tape) :
    ∀ n (s : Transcript), Prefix s.oracle (circle decode tape n s).2.oracle := by
  intro n
  induction n with
  | zero => intro s; exact prefix_refl _
  | succ n ih =>
      intro s
      simp only [circle]
      split
      · exact challenge_prefix tape s
      · split
        · exact prefix_trans (challenge_prefix tape s) (ih _)
        · exact challenge_prefix tape s

theorem circle_logs_start (decode : List Nat → Option Point) (tape : Tape) :
    ∀ n (s : Transcript),
      squeezeInput s.digest ∈ inputs (circle decode tape (n+1) s).2.oracle.log := by
  intro n
  induction n with
  | zero =>
      intro s
      cases h : (challenge tape s).1 with
      | none => simpa [circle, h] using challenge_logs_start tape s
      | some limbs =>
          cases hd : decode limbs with
          | none => simpa [circle, h, hd] using challenge_logs_start tape s
          | some point => simpa [circle, h, hd] using challenge_logs_start tape s
  | succ n ih =>
      intro s
      cases h : (challenge tape s).1 with
      | none => simpa [circle, h] using challenge_logs_start tape s
      | some limbs =>
          cases hd : decode limbs with
          | some point => simpa [circle, h, hd] using challenge_logs_start tape s
          | none =>
              have hp := circle_prefix decode tape (n+1) (challenge tape s).2
              simpa [circle, h, hd] using
                (mem_inputs_of_prefix hp (challenge_logs_start tape s))

theorem distinct_prefix [DecidableEq Point]
    (decode : List Nat → Option Point) (first : Point) (tape : Tape) :
    ∀ n (s : Transcript), Prefix s.oracle (distinct decode first tape n s).2.oracle := by
  intro n
  induction n with
  | zero => intro s; exact prefix_refl _
  | succ n ih =>
      intro s
      simp only [distinct]
      split
      · exact circle_prefix decode tape 3 s
      · split
        · exact prefix_trans (circle_prefix decode tape 3 s) (ih _)
        · exact circle_prefix decode tape 3 s

theorem distinct_logs_start [DecidableEq Point]
    (decode : List Nat → Option Point) (first : Point) (tape : Tape) :
    ∀ n (s : Transcript) (point : Point),
      (distinct decode first tape (n+1) s).1 = .ok point →
      squeezeInput s.digest ∈ inputs (distinct decode first tape (n+1) s).2.oracle.log := by
  intro n
  induction n with
  | zero =>
      intro s point success
      cases h : (circle decode tape 3 s).1 with
      | error error => simp [distinct, h] at success
      | ok point' =>
          by_cases heq : point' = first
          · simp [distinct, h, heq] at success
          · simpa [distinct, h, heq] using circle_logs_start decode tape 2 s
  | succ n ih =>
      intro s point success
      cases h : (circle decode tape 3 s).1 with
      | error error => simp [distinct, h] at success
      | ok point' =>
          by_cases heq : point' = first
          · have hm := mem_inputs_of_prefix (distinct_prefix decode first tape (n+1)
                (circle decode tape 3 s).2) (circle_logs_start decode tape 2 s)
            unfold distinct
            simp only [h, heq, ↓reduceIte]
            exact hm
          · simpa [distinct, h, heq] using circle_logs_start decode tape 2 s

#print axioms squeeze_logs_start
#print axioms challenge_logs_start
#print axioms circle_prefix
#print axioms circle_logs_start
#print axioms distinct_prefix
#print axioms distinct_logs_start

end AspisV8Completion.FSOODSamplerExposure
