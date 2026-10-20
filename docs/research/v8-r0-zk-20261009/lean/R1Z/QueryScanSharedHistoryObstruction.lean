import R1Z.QueryScanHistorySplit
import R1Z.PhaseSamplerParserBin
import R1Z.RomObserverBin

/-! A legal shared-ROM query-state self-loop. Re-reading a known address
is deterministic even though the unconditioned table is uniform. The scan
argument is symbolic in its words, prefix length and scan state. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanSharedHistoryObstruction
open R0Z R0Z.FsStatement R0Z.FsAbort R1Z.GamesR1 R1Z.LensR1
  R1Z.PhaseSamplerParserBin R1Z.PhaseQueryScanBin R1Z.QueryScanPrivacyFinal
  R1Z.QueryScanHistorySplit AspisV8R19.Q22WordScan
attribute [local instance] Classical.propDecidable

/-- Query read addresses are exactly the existing transcript grammar. -/
def squeezeAddress (s : OracleAnswer) : List UInt8 := ans s ++ [1]
def advanceAddress (s : OracleAnswer) : List UInt8 := ans s ++ [2]

def queryState (H : List UInt8 → OracleAnswer) (s : OracleAnswer) : ℕ → OracleAnswer
  | 0 => s
  | n+1 => H (advanceAddress (queryState H s n))

def queryBlocks (H : List UInt8 → OracleAnswer) (s : OracleAnswer) : Fin 8 → OracleAnswer :=
  fun k => H (squeezeAddress (queryState H s k.val))

theorem queryState_self_loop (H : List UInt8 → OracleAnswer) (s : OracleAnswer)
    (loop : H (advanceAddress s) = s) (n : ℕ) : queryState H s n = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [queryState, ih] using loop

theorem queryBlocks_self_loop (H : List UInt8 → OracleAnswer) (s : OracleAnswer)
    (loop : H (advanceAddress s) = s) : queryBlocks H s = fun _ => H (squeezeAddress s) := by
  funext k
  unfold queryBlocks
  rw [queryState_self_loop H s loop]

/-- Both addresses use the retained model grammar, including its LE bytes;
there is no invented query-counter domain separation in this example. -/
theorem transcript_query_addresses (rest : R1Z.TranscriptR1.Rest)
    (s : OracleAnswer) (k : Fin 8) :
    R1Z.TranscriptR1.addrWith (.qb k) s rest = squeezeAddress s ∧
    R1Z.TranscriptR1.addrWith (.qa k) s rest = advanceAddress s := ⟨rfl, rfl⟩

/-- The zero-answer history is actually reachable in the in-order evaluator
for every address program. This induction never unfolds the read count. -/
theorem zero_oracle_runN {A : Type} {m : ℕ}
    (a : Fin m → (Fin m → OracleAnswer) → A) (n : ℕ) :
    R1Z.LazyFrozen.runN a (fun _ => 0) 0 n = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [R1Z.LazyFrozen.runN_succ, ih]
      split
      · funext i
        simp only [Function.update_apply]
        split <;> rfl
      · rfl

theorem zero_oracle_runC {A : Type} {m : ℕ}
    (a : Fin m → (Fin m → OracleAnswer) → A) :
    R1Z.LazyFrozen.runC a (fun _ => 0) 0 = fun _ => 0 := zero_oracle_runN a m

theorem zero_table_lookup (bound : ℕ) :
    R1Z.RomFiniteBin.lookup bound (fun _ => 0) = fun _ => 0 := by
  funext bs
  unfold R1Z.RomFiniteBin.lookup
  cases R1Z.RomFiniteBin.decode bound bs <;> rfl

/-- The exhibited zero-answer history is reachable in the finite ROM used
by the endpoint, for its actual bound and any prover address program. -/
theorem finite_rom_zero_history (bound : ℕ) {m : ℕ}
    (a : Fin m → (Fin m → OracleAnswer) → List UInt8) :
    R1Z.LazyFrozen.runC a (R1Z.RomFiniteBin.lookup bound (fun _ => 0)) 0 = fun _ => 0 := by
  rw [zero_table_lookup]
  exact zero_oracle_runC a

/-- Scanning never invents a candidate. This induction also covers the stop
branches and the empty-list branch without reducing a 64-word recurrence. -/
theorem scan_alphabet (alphabet : Finset ℕ) (xs : List ℕ) (s : ScanState)
    (hs : ∀ x ∈ s.accepted, x ∈ alphabet) (hx : ∀ x ∈ xs, x ∈ alphabet) :
    ∀ x ∈ (scan s xs).1.accepted, x ∈ alphabet := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
      by_cases stop : s.accepted.length = 22 ∨ s.draws = 64
      · simpa only [scan, if_pos stop] using hs
      · simp only [scan, if_neg stop]
        apply ih
        · intro y hy
          rcases (AspisR1.QueryScanModelFailure.keep_mem _ _ _).mp hy with hy | rfl
          · exact hs y hy
          · exact hx y (List.mem_cons_self)
        · intro y hy
          exact hx y (List.mem_cons_of_mem _ hy)

theorem repeated_block_scan_bound (b : OracleAnswer) (k : Fin 8) :
    (scanned k (fun _ => b)).1.accepted.length ≤ 8 := by
  let alphabet := (blockWords b).toFinset
  have hm : ∀ x ∈ parsedWords (fun _ => b) k, x ∈ alphabet := by
    intro x hx
    obtain ⟨bb, hbb, hxb⟩ := List.mem_flatMap.mp hx
    have hbb' : bb ∈ List.ofFn (fun _ : Fin 8 => b) := List.mem_of_mem_take hbb
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hbb'
    have he : bb = b := hj.symm
    rw [he] at hxb
    exact List.mem_toFinset.mpr hxb
  have hs := scan_alphabet alphabet (parsedWords (fun _ => b) k)
    AspisR1.QueryScanModelFailure.initial (by simp [AspisR1.QueryScanModelFailure.initial]) hm
  have hsub : (scanned k (fun _ => b)).1.accepted.toFinset ⊆ alphabet := by
    intro x hx
    exact hs x (List.mem_toFinset.mp hx)
  have hn := AspisR1.QueryScanOrderedModel.scan_nodup
    AspisR1.QueryScanModelFailure.initial (parsedWords (fun _ => b) k)
    (by simp [AspisR1.QueryScanModelFailure.initial])
  calc _ = (scanned k (fun _ => b)).1.accepted.toFinset.card :=
          (List.toFinset_card_of_nodup hn).symm
       _ ≤ alphabet.card := Finset.card_le_card hsub
       _ ≤ (blockWords b).length := List.toFinset_card_le _
       _ = 8 := blockWords_length b

theorem repeated_block_finish_fails (b : OracleAnswer) (k : Fin 8) :
    ∃ count, finish (scanned k (fun _ => b)).1 = .error count := by
  have h := repeated_block_scan_bound b k
  exact ⟨_, finish_error_count _ (by omega)⟩

/-- Failure at the constructed parser's own selected first-stop endpoint,
not at a separately chosen or enumerated block index. -/
theorem shared_loop_finish_fails (H : List UInt8 → OracleAnswer) (s : OracleAnswer)
    (loop : H (advanceAddress s) = s) :
    ∃ count, finish (scanned (stop done (queryBlocks H s)) (queryBlocks H s)).1 = .error count := by
  rw [queryBlocks_self_loop H s loop]
  exact repeated_block_finish_fails _ _

/-- With the release-sized domain, both self-loop read addresses are valid;
the example does not rely on the lookup fallback outside the finite ROM. -/
theorem loop_addresses_in_domain (bound : ℕ) (hbound : 33 ≤ bound) (s : OracleAnswer) :
    squeezeAddress s ∈ R1Z.RomFiniteBin.domain bound ∧
    advanceAddress s ∈ R1Z.RomFiniteBin.domain bound := by
  constructor <;> apply (R1Z.RomFiniteBin.mem_domain _ _).mpr <;>
    simpa only [squeezeAddress, advanceAddress, List.length_append, length_ans,
      List.length_singleton] using hbound

/-- This history is inhabited in the existing finite byte-string ROM. The
only condition is a previously seen advance answer, not a source assumption. -/
abbrev LoopHistory (bound : ℕ) :=
  {tab : R1Z.RomFiniteBin.Address bound → OracleAnswer //
    R1Z.RomFiniteBin.lookup bound tab (advanceAddress 0) = 0}

instance loopHistory_nonempty (bound : ℕ) : Nonempty (LoopHistory bound) := by
  refine ⟨⟨fun _ => 0, ?_⟩⟩
  unfold R1Z.RomFiniteBin.lookup
  cases R1Z.RomFiniteBin.decode bound (advanceAddress 0) <;> rfl

/-- Conditioning on this retained advance answer leaves mass-one failure.
The claim holds for every bound, including the release ROM bound. -/
theorem reached_shared_history_failure_mass (bound : ℕ) :
    eventMass (fun tab : LoopHistory bound =>
      ∃ count, finish (scanned
        (stop done (queryBlocks (R1Z.RomFiniteBin.lookup bound tab.val) 0))
        (queryBlocks (R1Z.RomFiniteBin.lookup bound tab.val) 0)).1 = .error count) = 1 := by
  have hh : ∀ tab : LoopHistory bound,
      ∃ count, finish (scanned
        (stop done (queryBlocks (R1Z.RomFiniteBin.lookup bound tab.val) 0))
        (queryBlocks (R1Z.RomFiniteBin.lookup bound tab.val) 0)).1 = .error count :=
    fun tab => shared_loop_finish_fails _ _ tab.property
  unfold eventMass
  simp only [hh, if_true]
  exact mean_const 1

theorem reached_shared_history_not_bounded (bound : ℕ) :
    ¬ eventMass (fun tab : LoopHistory bound =>
      ∃ count, finish (scanned
        (stop done (queryBlocks (R1Z.RomFiniteBin.lookup bound tab.val) 0))
        (queryBlocks (R1Z.RomFiniteBin.lookup bound tab.val) 0)).1 = .error count) ≤ scanProbability := by
  rw [reached_shared_history_failure_mass]
  exact not_le_of_gt scanProbability_lt_one

#print axioms queryState_self_loop
#print axioms queryBlocks_self_loop
#print axioms transcript_query_addresses
#print axioms zero_oracle_runN
#print axioms zero_oracle_runC
#print axioms zero_table_lookup
#print axioms finite_rom_zero_history
#print axioms scan_alphabet
#print axioms repeated_block_scan_bound
#print axioms repeated_block_finish_fails
#print axioms shared_loop_finish_fails
#print axioms loop_addresses_in_domain
#print axioms reached_shared_history_failure_mass
#print axioms reached_shared_history_not_bounded
end R1Z.QueryScanSharedHistoryObstruction
