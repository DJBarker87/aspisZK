import R1Z.ProverCommitFuel22
/-! Counter accounting for the actual extracted coin transition. The three
searches are the nonce and two secrets consumed in sim::tape. Successful
runs within five draws each stay below 15; this does not assume termination
on every hash or establish freshness against unrelated oracle queries. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCounter24
open Aeneas Aeneas.Std Result ProverCommitSimulatorCoin18 ProverCommitFuel22

theorem next_counter (hash : Hash) (seed answer : Bytes32) (attempt : U32)
    (stream : U8) (counter next : U64)
    (step : AspisR1SimulatorCoin18.sim.coin_owned18 hash seed attempt stream counter =
      ok (answer,next)) : next = U64.wrapping_add counter 1#u64 := by
  rw [extracted_step] at step
  cases h : hash (frame seed attempt stream counter) with
  | fail e => simp only [h,bind_tc_fail] at step; cases step
  | div => simp only [h,bind_tc_div] at step; cases step
  | ok value =>
    simp only [h,bind_tc_ok] at step
    exact (congrArg Prod.snd (Result.ok.inj step)).symm

theorem advance_no_wrap (counter : U64) (room : counter.val+1 < 2^64) :
    (U64.wrapping_add counter 1#u64).val = counter.val+1 := by
  rw [U64.wrapping_add_val_eq]
  simpa only [UScalar.size_def,UScalarTy.U64_numBits_eq,
    show (1#u64).val = 1 from rfl] using Nat.mod_eq_of_lt room

theorem positive {zero : Bytes32} {hash : Hash} {seed : Bytes32}
    {attempt : U32} {stream : U8} {n : Nat} {counter final : U64} {answer : Bytes32}
    (run : Finishes zero hash seed attempt stream n counter answer final) : 0 < n := by
  cases run <;> omega

/-- The final counter is exactly the initial counter plus all consumed
reads, including rejected zero answers. There is no off-by-one reset. -/
theorem accounting {zero : Bytes32} {hash : Hash} {seed : Bytes32}
    {attempt : U32} {stream : U8} {n : Nat} {counter final : U64} {answer : Bytes32}
    (run : Finishes zero hash seed attempt stream n counter answer final)
    (room : counter.val+n < 2^64) : final.val = counter.val+n := by
  induction run with
  | found counter next answer step nonzero =>
    rw [next_counter hash seed answer attempt stream counter next step]
    exact advance_no_wrap counter room
  | retry n counter middle final answer step rest ih =>
    have middle_eq := next_counter hash seed zero attempt stream counter middle step
    have middle_val : middle.val = counter.val+1 := by
      rw [middle_eq]
      exact advance_no_wrap counter (by omega)
    have tail_room : middle.val+n < 2^64 := by omega
    have tail := ih tail_room
    omega

/-- Good-path room for all three source nonzero calls, sharing stream 3 and
one retained counter, rather than three independently reset counters. -/
theorem three_search_room {zero : Bytes32} {hash : Hash} {seed : Bytes32}
    {attempt : U32} {n₁ n₂ n₃ : Nat} {c₁ c₂ c₃ : U64} {a b c : Bytes32}
    (first : Finishes zero hash seed attempt 3#u8 n₁ 0#u64 a c₁)
    (second : Finishes zero hash seed attempt 3#u8 n₂ c₁ b c₂)
    (third : Finishes zero hash seed attempt 3#u8 n₃ c₂ c c₃)
    (bound₁ : n₁ ≤ 5) (bound₂ : n₂ ≤ 5) (bound₃ : n₃ ≤ 5) :
    c₁.val = n₁ ∧ c₂.val = n₁+n₂ ∧ c₃.val = n₁+n₂+n₃ ∧
      c₃.val ≤ 15 ∧ c₃.val+5 < 2^64 := by
  have h₁ : c₁.val = n₁ := by
    have h := accounting first (by change 0+n₁ < 2^64; omega)
    simpa only [show (0#u64).val = 0 from rfl,Nat.zero_add] using h
  have h₂ := accounting second (by omega)
  have h₃ := accounting third (by omega)
  exact ⟨h₁,by omega,by omega,by omega,by omega⟩

/-- Executable bounded adapter for precisely the three coin searches. It
retains the counter between calls; no new sampling policy is introduced. -/
def three (zero : Bytes32) (hash : Hash) (seed : Bytes32) (attempt : U32)
    (fuel : Nat) (counter : U64) : Result (Option (Bytes32 × Bytes32 × Bytes32 × U64)) := do
  let first ← ProverCommitNonzero20.search zero hash seed attempt 3#u8 fuel counter
  match first with
  | none => ok none
  | some (a,c₁) =>
    let second ← ProverCommitNonzero20.search zero hash seed attempt 3#u8 fuel c₁
    match second with
    | none => ok none
    | some (b,c₂) =>
      let third ← ProverCommitNonzero20.search zero hash seed attempt 3#u8 fuel c₂
      match third with
      | none => ok none
      | some (c,c₃) => ok (some (a,b,c,c₃))

theorem three_agrees {zero : Bytes32} {hash : Hash} {seed : Bytes32}
    {attempt : U32} {n₁ n₂ n₃ fuel : Nat} {start c₁ c₂ c₃ : U64} {a b c : Bytes32}
    (first : Finishes zero hash seed attempt 3#u8 n₁ start a c₁)
    (second : Finishes zero hash seed attempt 3#u8 n₂ c₁ b c₂)
    (third : Finishes zero hash seed attempt 3#u8 n₃ c₂ c c₃)
    (bound₁ : n₁ ≤ fuel) (bound₂ : n₂ ≤ fuel) (bound₃ : n₃ ≤ fuel) :
    three zero hash seed attempt fuel start = ok (some (a,b,c,c₃)) := by
  simp only [three,agrees first fuel bound₁,agrees second fuel bound₂,
    agrees third fuel bound₃,bind_tc_ok]

#print axioms next_counter
#print axioms advance_no_wrap
#print axioms positive
#print axioms accounting
#print axioms three_search_room
#print axioms three_agrees
end R1Z.ProverCommitCounter24
