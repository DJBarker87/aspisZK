import R1Z.PhaseQueryScanBin
import R1J.PrivacySamplerSpend
import R1Z.PhaseCircleBlocksBin
import QueryScanOrderedModel

/-! Concrete block samplers and retained word-parser/first-22 policy.
The scan tests completion before the next word, as Q22WordScan actually does;
completion on a block's eighth word can therefore consume the next block.
These are Lean-model identities. Rust execution/history correspondence remains
a separate source join, including the rejected/exhausted outcome. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseSamplerParserBin
open R0Z.FsStatement R1Z.GamesR1 R1Z.GamesR1PBin R1Z.PhaseLocalityBin
  R1Z.PhaseQueryScanBin AspisV8R19.Q22WordScan
attribute [local instance] Classical.propDecidable

local notation "K" => AspisWideTower.WideExact

def state (b : OracleAnswer) : AspisV8R19.SourceDuplexStep.State :=
  R1J.SamplerLawSpend.stateEquiv b

def scalar (b : OracleAnswer) : K :=
  R1J.SamplerLawSpend.s1Spend
    (algebraMap R1J.SamplerLawSpend.QF K) b

/-- The small block-circle adapter keeps concrete tower typeclass reduction
out of the combined sampler/ROM import closure. -/
abbrev circle := PhaseCircleBlocksBin.select

def openingScalar (i : Fin 4) (b : OracleAnswer) : K :=
  if i = 0 then (R0C.ModuloField.gammaNZ (state b)).val
  else R0C.ModuloField.ordinary (state b)

/-- Eight little-endian words, masked to 18 bits, in their source order. -/
def blockWords (b : OracleAnswer) : List ℕ := AspisV8R19.SamplerWords.words 18 (state b)

def parsedWords (q : Fin 8 → OracleAnswer) (k : Fin 8) : List ℕ :=
  ((List.ofFn q).take (k.val + 1)).flatMap blockWords

theorem parsed_observed (q : Fin 8 → OracleAnswer) (k : Fin 8) :
    parsedWords (observed q k) k = parsedWords q k := by
  unfold parsedWords
  apply congrArg (fun blocks : List OracleAnswer => blocks.flatMap blockWords)
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
  · intro n hn hn'
    have hn0 := hn
    simp only [List.length_take, List.length_ofFn] at hn0
    simp only [List.getElem_take, List.getElem_ofFn]
    unfold observed
    exact if_pos (by change n ≤ k.val; omega)

theorem parsedWords_bounded (q : Fin 8 → OracleAnswer) (k : Fin 8)
    (n : ℕ) (hn : n ∈ parsedWords q k) : n < 262144 := by
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hn
  exact AspisV8R19.SamplerWords.words_bounded 18 (state b) n hb

def scanned (k : Fin 8) (q : Fin 8 → OracleAnswer) : ScanState × Bool :=
  scan AspisR1.QueryScanModelFailure.initial (parsedWords q k)

def done (k : Fin 8) (q : Fin 8 → OracleAnswer) : Prop := (scanned k q).2 = true

def fibre (n : ℕ) : Fib := ⟨n % 262144, Nat.mod_lt _ (by decide)⟩

def decoded (k : Fin 8) (q : Fin 8 → OracleAnswer) : Finset Fib :=
  ((scanned k q).1.accepted.map fibre).toFinset

def querySet (q : Fin 8 → OracleAnswer) : Finset Fib := queries done decoded q

def decode (s : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer)
    (q : Fin 8 → OracleAnswer) (_rho : OracleAnswer) : R0Z.HonestView.Challenges K where
  sem := fun i => scalar (s ⟨i.val, by omega⟩)
  circle := fun i => circle i (s ⟨25+i.val, by omega⟩)
  opening := fun i => openingScalar i (o i)
  queries := querySet q

theorem decode_local : DecodeLocal decode where
  sem := fun _ _ _ _ _ _ _ _ _ he => congrArg scalar he
  circle := fun _ _ _ _ _ _ _ _ i he => congrArg (circle i) he
  opening := fun _ _ _ _ _ _ _ _ i he => congrArg (openingScalar i) he
  queries := fun _ _ _ _ _ _ _ => rfl

theorem gamma_nonzero (b : OracleAnswer) : openingScalar 0 b ≠ 0 :=
  (R0C.ModuloField.gammaNZ (state b)).property

theorem blockWords_length (b : OracleAnswer) : (blockWords b).length = 8 :=
  AspisV8R19.SamplerWords.words_length 18 (state b)

theorem blockWords_bounded (b : OracleAnswer) (n : ℕ) (hn : n ∈ blockWords b) :
    n < 262144 := AspisV8R19.SamplerWords.words_bounded 18 (state b) n hn

/-- A successful prefix gives exactly the source model's first 22 distinct
words, in stable order; no sorting of the accepted list is introduced. -/
theorem parsed_first22 (q : Fin 8 → OracleAnswer) (k : Fin 8) (out : List ℕ)
    (he : finish (scanned k q).1 = .ok out) :
    out = ((parsedWords q k).foldl keep []).take 22 :=
  AspisR1.QueryScanOrderedModel.successful_first22
    AspisR1.QueryScanModelFailure.initial (parsedWords q k) out (by simp [AspisR1.QueryScanModelFailure.initial]) he

theorem decoded_success (q : Fin 8 → OracleAnswer) (k : Fin 8) (out : List ℕ)
    (he : finish (scanned k q).1 = .ok out) :
    decoded k q = (out.map fibre).toFinset := by
  unfold finish at he
  split at he
  · have hs := Except.ok.inj he
    unfold decoded
    rw [hs]
  · cases he

theorem query_success (q : Fin 8 → OracleAnswer) (out : List ℕ)
    (he : finish (scanned (stop done q) q).1 = .ok out) :
    querySet q = (out.map fibre).toFinset ∧
      out = ((parsedWords q (stop done q)).foldl keep []).take 22 := by
  have hp : scanned (stop done q) (observed q (stop done q)) = scanned (stop done q) q := by
    unfold scanned
    rw [parsed_observed]
  constructor
  · exact decoded_success (observed q (stop done q)) (stop done q) out (by rw [hp]; exact he)
  · exact parsed_first22 q (stop done q) out he

theorem no_earlier_completion (q : Fin 8 → OracleAnswer) (k : Fin 8)
    (hk : k < stop done q) : ¬ done k (observed q k) := by
  intro hd
  have hl := stop_le done q k (by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hd⟩)
  exact (not_lt_of_ge hl) hk

theorem query_prefix (q q' : Fin 8 → OracleAnswer)
    (he : PrefixAgree q q' (stop done q)) :
    stop done q = stop done q' ∧ querySet q = querySet q' :=
  ⟨stop_local done q q' he, queries_local done decoded q q' he⟩

/-- The eighth block is the explicit fallback endpoint even if readiness
never occurs. Failure remains visible in finish; it is not a successful Q22. -/
theorem exhausted_endpoint (q : Fin 8 → OracleAnswer)
    (he : ∀ k, ¬ done k (observed q k)) : stop done q = 7 := by
  have hm := stop_mem done q
  have hd : done (stop done q) (observed q (stop done q)) ∨ stop done q = 7 :=
    (Finset.mem_filter.mp hm).2
  exact hd.resolve_left (he _)

def wireData {CommitHandle Aux : Type} (base : R1Wire K CommitHandle Aux) :
    R1Wire K CommitHandle Aux := { base with dec := decode, kstarOf := stop done }

def rows01 {CommitHandle Aux : Type} (base : R1Wire K CommitHandle Aux) :
    R1Z.Sem1UniformR1.SemRows01 (wireData base) where
  s1 := scalar
  sem1 := fun _ _ _ _ => rfl
  sem0 := fun _ _ _ _ _ he => congrArg scalar (he 0 (by decide))

theorem rows01_source {CommitHandle Aux : Type} (base : R1Wire K CommitHandle Aux) :
    (rows01 base).s1 = R1J.SamplerLawSpend.s1Spend (algebraMap R1J.SamplerLawSpend.QF K) := rfl

#print axioms parsedWords_bounded
#print axioms no_earlier_completion
#print axioms parsed_observed
#print axioms query_success
#print axioms decode_local
#print axioms gamma_nonzero
#print axioms blockWords_length
#print axioms blockWords_bounded
#print axioms parsed_first22
#print axioms decoded_success
#print axioms query_prefix
#print axioms exhausted_endpoint
#print axioms rows01
#print axioms rows01_source
end R1Z.PhaseSamplerParserBin
