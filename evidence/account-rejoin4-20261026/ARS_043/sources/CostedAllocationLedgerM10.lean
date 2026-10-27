import CostedExtractorStagesM10
import CubicFieldBoundM10
import CountDominanceM10
import GSActualByteJobsM10
import RawExtractorFixedCubicM10
import InitialPublicImageWorkM10

/-! Complete work/value ledger with one explicitly residual component:
cumulative allocator bit work. `HeapMirror` is data, not a claim that an
arbitrary function is a source allocator. Instantiating it requires the actual
allocation annotation. AllocationBound is the sole remaining implementation
hypothesis; no allocation fact is inferred from equal returned values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CostedAllocationLedgerM10
open AspisWideTower AspisV8R15.ExactTowerBase RawExtractorCostComposedV2
open RawExtractorCostLedger
open RawRecordedEagerExtractorReadsBin (RunView)
open M31AcceptFiber
attribute [local irreducible] InitialPublicImageWorkM10.budget GSActualBankJobsM10.count GSBankOutputEnvelopeM10.candidates

structure HeapMirror where
  bits : RunView → Coins → Nat

@[never_extract,noinline,irreducible] def footprint : Nat :=
  100*(GSBankOutputEnvelopeM10.candidates+1)^60*(29*1024+1000)+
    (6291456+6480098+1)^4+(RRRecoveryWorkM10.cap 114689 112 1025+2)^4+
    21377328*1024+InitialPublicImageWorkM10.budget+1000000000000

@[never_extract,noinline,irreducible] def workConstant : Nat :=
  CostedExtractorStagesM10.workConstant InitialPublicImageWorkM10.budget

/-- Cumulative allocation-bit work alone on the original ledger domain.
Field/control work, value equality, reads and Jobs are not assumptions here. -/
def AllocationBound (heap : HeapMirror) (Q : Nat) : Prop := ∀ run coins,
  run.2.2 = true → run.1.length ≤ Q+1161 → heap.bits run coins ≤ (footprint*workConstant)*(run.1.length+1)

@[never_extract,noinline,irreducible] def naturalConstant : Nat :=
  2^(RRRecoveryWorkM10.cap 114689 112 1025+2)+(P31^8)+2^64+
    footprint+workConstant+1

@[never_extract,noinline,irreducible] def scale : Nat :=
  CubicAllocationLiftM10.constant workConstant (footprint*workConstant) naturalConstant

@[irreducible] def eval (heap : HeapMirror) (run : RunView) (coins : Coins) :
    Option SpendRelation.Wspend × Resources :=
  let x := CostedExtractorStagesM10.eval InitialPublicImageWorkM10.image
    InitialPublicImageWorkM10.budget InitialPublicImageWorkM10.bounded run coins
  (x.1,CubicAllocationLiftM10.resources x.2 (BinEagerWordsReads.words run).2
    (heap.bits run coins) run.1.length naturalConstant)

theorem value (heap : HeapMirror) (run : RunView) (coins : Coins) :
    (eval heap run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  unfold eval
  exact CostedExtractorStagesM10.value _ _ _ run coins

@[irreducible] def extractor (heap : HeapMirror) : RawExtractorCostComposedBin.CostedExtractor :=
  ⟨eval heap,value heap⟩


theorem work_bound (run : RunView) (coins : Coins) :
    (CostedExtractorStagesM10.eval InitialPublicImageWorkM10.image InitialPublicImageWorkM10.budget
      InitialPublicImageWorkM10.bounded run coins).2 ≤ workConstant*(run.1.length+1) := by
  unfold workConstant
  exact CostedExtractorStagesM10.work _ _ _ run coins

theorem total (heap : HeapMirror) (Q : Nat) (h_M10_allocation : AllocationBound heap Q)
    (run : RunView) (coins : Coins) (ha : run.2.2 = true) (hl : run.1.length ≤ Q+1161) :
    (eval heap run coins).2.total ≤ 4*scale^3*(run.1.length+1)^3 := by
  unfold eval scale
  exact CubicAllocationLiftM10.total_bound _ _ _ _ _ _ _
    (work_bound run coins) (BinEagerWordsReads.words_reads run)
    (h_M10_allocation run coins ha hl)

@[never_extract,noinline] def fixed : Parameters where
  n := 2000000
  logSize := 1161
  listSize := footprint
  b := P31^8+1
  calls := GSActualBankJobsM10.count 149+1
  depth := 1025
  ell := 112
  retries := 149
  overheadConstant := 4*scale^3
  overheadDegree := 3

def params (Q : Nat) : Parameters := RawExtractorFixedCubicM10.family fixed Q

theorem jobs_mono (j : Jobs WideExact) (n b count n' b' count' : Nat)
    (h : j.Bounded n b count) (hn : n ≤ n') (hb : b ≤ b') (hc : count ≤ count') :
    j.Bounded n' b' count' :=
  ⟨h.gcd_count.trans hc,h.division_count.trans hc,h.power_count.trans hc,
    fun pq hp => ⟨(h.gcd_sizes pq hp).1.trans hn,(h.gcd_sizes pq hp).2.trans hn⟩,
    fun d hd => (h.division_sizes d hd).trans hn,
    fun p hp => (h.power_bits p hp).trans hb⟩

theorem count_le (Q : Nat) : GSActualBankJobsM10.count 149 ≤ (params Q).count := by
  unfold params RawExtractorFixedCubicM10.family fixed Parameters.count
  exact CountDominanceM10.bound (GSActualBankJobsM10.count 149) (1025*112+1) (149+1) (112+1)
    (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)

theorem lift_log (x L Q : Nat) (h : x ≤ 4*scale^3*(L+1)^3) (hl : L ≤ Q+1161) :
    x ≤ (params Q).overhead := by
  have hl' : L+1 ≤ 2000000+(Q+1161)+footprint+(P31^8+1)+1 := by omega
  unfold params RawExtractorFixedCubicM10.family fixed Parameters.overhead
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl' 3))

theorem field_bound (heap : HeapMirror) (run : RunView) (coins : Coins) :
    (eval heap run coins).2.fieldOps ≤ 4*scale^3*(run.1.length+1)^3 := by
  unfold eval CubicAllocationLiftM10.resources
  change (CostedExtractorStagesM10.eval InitialPublicImageWorkM10.image InitialPublicImageWorkM10.budget
      InitialPublicImageWorkM10.bounded run coins).2 ≤ _
  unfold scale
  exact CubicFieldBoundM10.bound _ _ _ _ _ (work_bound run coins)

theorem total_overhead (heap : HeapMirror) (Q : Nat) (h_M10_allocation : AllocationBound heap Q)
    (run : RunView) (coins : Coins) (ha : run.2.2 = true) (hl : run.1.length ≤ Q+1161) :
    (eval heap run coins).2.total ≤ (params Q).overhead :=
  lift_log _ _ Q (total heap Q h_M10_allocation run coins ha hl) hl

theorem bounded_jobs (heap : HeapMirror) (Q : Nat) (run : RunView) (coins : Coins)
    (hl : run.1.length ≤ Q+1161) :
    ∃ j : Jobs WideExact, j.Bounded (params Q).n (params Q).b (params Q).count ∧
      (eval heap run coins).2.fieldOps ≤ j.charge (params Q).mulBudget+(params Q).overhead := by
  let words := (BinPublicRecoverySharedStageM10.stage run).1
  let inputs := (GSPointBatchWorkM10.inputs (CostedExtractorStagesM10.received words)
    (fun _ => words.final)).1
  let j := GSActualByteJobsM10.jobs inputs coins
  have hj := jobs_mono j 113 (P31^8+1) (GSActualBankJobsM10.count 149)
    (params Q).n (params Q).b (params Q).count
    (GSActualByteJobsM10.jobs_bounded inputs coins) (by change 113 ≤ 2000000; omega)
    (Nat.le_refl _) (count_le Q)
  refine ⟨j,hj,?_⟩
  have hf := lift_log _ _ Q (field_bound heap run coins) hl
  exact hf.trans (Nat.le_add_left _ _)

theorem reads (heap : HeapMirror) (Q : Nat) (run : RunView) (coins : Coins)
    (hl : run.1.length ≤ Q+1161) : (eval heap run coins).2.logReads ≤ (params Q).readBudget := by
  have hh := (BinEagerWordsReads.words_reads run).trans (Nat.mul_le_mul_left 12976224 hl)
  unfold eval CubicAllocationLiftM10.resources
  change (BinEagerWordsReads.words run).2 ≤ 7*2000000*(Q+1161)
  exact hh.trans (Nat.mul_le_mul_right (Q+1161) (show 12976224 ≤ 7*2000000 by omega))

theorem ledger (heap : HeapMirror) (Q : Nat) (h_M10_allocation : AllocationBound heap Q) :
    RawExtractorCostComposedBin.LedgerRefinement (extractor heap) (params Q) Q := by
  unfold extractor
  constructor
  · exact Nat.le_refl _
  · intro run coins _ hl
    exact bounded_jobs heap Q run coins hl
  · intro run coins _ hl
    exact reads heap Q run coins hl
  · intro run coins ha hl
    have ht := total_overhead heap Q h_M10_allocation run coins ha hl
    have hb : (eval heap run coins).2.bits ≤ (eval heap run coins).2.total := by
      unfold Resources.total
      omega
    have hf : 1 ≤ ((params Q).b+1)^2 := by
      have hh := Nat.pow_le_pow_left (show 1 ≤ (params Q).b+1 by omega) 2
      simpa only [one_pow] using hh
    have hm := Nat.mul_le_mul
      (show (params Q).overhead ≤ (eval heap run coins).2.fieldOps+
        (eval heap run coins).2.logReads+(params Q).overhead by omega) hf
    change (eval heap run coins).2.bits ≤ _
    exact (hb.trans ht).trans (by simpa only [Nat.mul_one] using hm)

theorem uniform (Q : Nat) : RawExtractorParameterPolynomial.CoordinateBound (params Q)
    (Q+RawExtractorFixedCubicM10.slack fixed) fixed.overheadConstant 3 :=
  RawExtractorFixedCubicM10.coordinates fixed Q

def costPolynomial : Polynomial Nat := RawExtractorFixedCubicM10.budgetPolynomial fixed

theorem polynomial_eval (Q : Nat) : costPolynomial.eval Q = (params Q).attemptBudget :=
  RawExtractorFixedCubicM10.budget_eval fixed Q

theorem polynomial_degree : costPolynomial.natDegree ≤ 3 := RawExtractorFixedCubicM10.budget_degree fixed


theorem accepted_cost (heap : HeapMirror) (Q : Nat) (h_M10_allocation : AllocationBound heap Q)
    (run : RunView) (ha : run.2.2 = true) (hl : run.1.length ≤ Q+1161) :
    (∀ coins, ((extractor heap).eval run coins).2.total ≤ costPolynomial.eval Q) ∧
    AspisV8R19.OracleResampling.mean (fun coins : Coins =>
      (((extractor heap).eval run coins).2.total : ℚ)) ≤ ((costPolynomial.eval Q : Nat) : ℚ) := by
  rw [polynomial_eval]
  exact RawExtractorCostComposedBin.accepted_attempt_cost (extractor heap) (params Q) Q
    (ledger heap Q h_M10_allocation) run ha hl

theorem direct_bound (heap : HeapMirror) (Q : Nat) (h_M10_allocation : AllocationBound heap Q)
    (run : RunView) (coins : Coins) (ha : run.2.2 = true) (hl : run.1.length ≤ Q+1161) :
    (eval heap run coins).2.total ≤ 4*scale^3*(Q+1162)^3 :=
  (total heap Q h_M10_allocation run coins ha hl).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))

#print axioms value
#print axioms work_bound
#print axioms total
#print axioms jobs_mono
#print axioms count_le
#print axioms lift_log
#print axioms field_bound
#print axioms total_overhead
#print axioms bounded_jobs
#print axioms reads
#print axioms ledger
#print axioms uniform
#print axioms polynomial_eval
#print axioms polynomial_degree
#print axioms accepted_cost
#print axioms direct_bound
end AspisR1.CostedAllocationLedgerM10
end
