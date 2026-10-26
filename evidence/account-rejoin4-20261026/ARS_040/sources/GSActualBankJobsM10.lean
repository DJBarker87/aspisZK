import RRRecoveryJobsM10
import GSDecoderActualBankM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSActualBankJobsM10
open CompPoly GSFixedInputDecoderFamily
open GSScalarCallScheduleM10 GSScalarOperandEnvelopeM10 RawExtractorCostLedger
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
attribute [local irreducible] GSConcreteInterpolation.initial GSConcreteInterpolation.final
  GSConcreteInterpolation.initialState GSConcreteInterpolation.finalState
  RRRecoveryJobsM10.select RRRecoveryJobsM10.calls RRActualScalarTraceBoundsM10.budget

def initial (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : InitialTape K t) : List (Call K) :=
  RRRecoveryJobsM10.select (GSConcreteInterpolation.initial points) (fun Q hr =>
    RRRecoveryJobsM10.calls 112 q t 1025 (GSConcreteInterpolation.initialState Q)
      (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
      (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H)

def final (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : FinalTape K t) : List (Call K) :=
  RRRecoveryJobsM10.select (GSConcreteInterpolation.final points) (fun Q hr =>
    RRRecoveryJobsM10.calls 112 q t 256 (GSConcreteInterpolation.finalState Q)
      (GSConcreteInterpolation.final_state_contract points hs Q hr).2.1
      (GSConcreteInterpolation.final_state_contract points hs Q hr).2.2 H)

theorem initial_length (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (hq : q = Fintype.card K) (H : InitialTape K t) :
    (initial q t points hs H).length ≤ RRActualScalarTraceBoundsM10.budget 112 t 1025 := by
  unfold initial
  apply RRRecoveryJobsM10.select_property (GSConcreteInterpolation.initial points) _
    (fun xs => xs.length ≤ RRActualScalarTraceBoundsM10.budget 112 t 1025)
  · exact Nat.zero_le _
  · intro Q hr
    exact RRRecoveryJobsM10.length _ _ _ _ _ _ _ hq _

theorem final_length (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (hq : q = Fintype.card K) (H : FinalTape K t) :
    (final q t points hs H).length ≤ RRActualScalarTraceBoundsM10.budget 112 t 256 := by
  unfold final
  apply RRRecoveryJobsM10.select_property (GSConcreteInterpolation.final points) _
    (fun xs => xs.length ≤ RRActualScalarTraceBoundsM10.budget 112 t 256)
  · exact Nat.zero_le _
  · intro Q hr
    exact RRRecoveryJobsM10.length _ _ _ _ _ _ _ hq _

theorem initial_bounded (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : InitialTape K t) : ∀ c ∈ initial q t points hs H, Bounded 112 q c := by
  unfold initial
  apply RRRecoveryJobsM10.select_property (GSConcreteInterpolation.initial points) _
    (fun xs => ∀ c ∈ xs, Bounded 112 q c)
  · simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true,forall_const]
  · intro Q hr
    exact RRRecoveryJobsM10.bounded _ _ _ _ _ _ _ (by omega) _

theorem final_bounded (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : FinalTape K t) : ∀ c ∈ final q t points hs H, Bounded 112 q c := by
  unfold final
  apply RRRecoveryJobsM10.select_property (GSConcreteInterpolation.final points) _
    (fun xs => ∀ c ∈ xs, Bounded 112 q c)
  · simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true,forall_const]
  · intro Q hr
    exact RRRecoveryJobsM10.bounded _ _ _ _ _ _ _ (by omega) _

def calls (q t : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) : List (Call K) :=
  GSScalarBatchJobsM10.flatten (List.finRange 29)
    (fun i => initial q t (inputs.initialPoints i) (inputs.initialSize i) H.1) ++
  GSScalarBatchJobsM10.flatten (List.finRange 5)
    (fun i => final q t (inputs.finalPoints i) (inputs.finalSize i) H.2)

@[never_extract,noinline] def count (t : Nat) : Nat :=
  29*RRActualScalarTraceBoundsM10.budget 112 t 1025+5*RRActualScalarTraceBoundsM10.budget 112 t 256

theorem calls_length (q t : Nat) (inputs : Inputs K 5) (hq : q = Fintype.card K)
    (H : InitialTape K t × FinalTape K t) : (calls q t inputs H).length ≤ count t := by
  have ha := GSScalarBatchJobsM10.length (List.finRange 29)
    (fun i => initial q t (inputs.initialPoints i) (inputs.initialSize i) H.1)
    (RRActualScalarTraceBoundsM10.budget 112 t 1025) (fun _ _ => initial_length _ _ _ _ hq _)
  have hb := GSScalarBatchJobsM10.length (List.finRange 5)
    (fun i => final q t (inputs.finalPoints i) (inputs.finalSize i) H.2)
    (RRActualScalarTraceBoundsM10.budget 112 t 256) (fun _ _ => final_length _ _ _ _ hq _)
  simpa only [calls,count,List.length_append,List.length_finRange] using Nat.add_le_add ha hb

theorem calls_bounded (q t : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) :
    ∀ c ∈ calls q t inputs H, Bounded 112 q c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact GSScalarBatchJobsM10.bounded _ _ 112 q (fun _ _ => initial_bounded _ _ _ _ _) c hc
  · exact GSScalarBatchJobsM10.bounded _ _ 112 q (fun _ _ => final_bounded _ _ _ _ _) c hc

def jobs (q t : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) : Jobs K :=
  GSScalarJobsM10.ofCalls 112 q (calls q t inputs H) (calls_bounded q t inputs H)

theorem jobs_bounded (q t : Nat) (inputs : Inputs K 5) (hq : q = Fintype.card K)
    (H : InitialTape K t × FinalTape K t) : (jobs q t inputs H).Bounded 113 (q+1) (count t) := by
  have hj := GSScalarJobsM10.bounded 112 q _ (calls_bounded q t inputs H)
  have hc := calls_length q t inputs hq H
  exact ⟨hj.gcd_count.trans hc,hj.division_count.trans hc,hj.power_count.trans hc,
    hj.gcd_sizes,hj.division_sizes,hj.power_bits⟩

#print axioms initial_length
#print axioms final_length
#print axioms initial_bounded
#print axioms final_bounded
#print axioms calls_length
#print axioms calls_bounded
#print axioms jobs_bounded
end AspisR1.GSActualBankJobsM10
end
