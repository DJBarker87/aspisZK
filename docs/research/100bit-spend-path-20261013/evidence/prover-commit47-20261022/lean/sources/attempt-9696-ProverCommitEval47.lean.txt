import R1Z.ProverCommitValueRange47
import R0.Chord
/-! Natural-basis evaluator and its payload meaning. These are exact-field
identities, not a certificate that a native loop implements this evaluator. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEval47
open ProverCommitValueRange47
open AspisCircleTensorBinding AspisR0.Chord
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity
open scoped BigOperators

variable {K : Type} [Field K]

def pairEval (q : Fin 1024 → K) (x : K) : K × K :=
  (∑ i : Fin 512, q ⟨2*i.val,by omega⟩ * naturalLineValue x i.val,
   ∑ i : Fin 512, q ⟨2*i.val+1,by omega⟩ * naturalLineValue x i.val)

def messageEval (q : Fin 1024 → K) (x y : K) : K :=
  (pairEval q x).1 + y * (pairEval q x).2

/-- The natural-basis dot products match the retained model's polynomial
semantics at every point, not just stored/domain points. -/
theorem message_model [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (q : Fin 1024 → K) (z : AspisR0.ChordGeometry.Point K) :
    messageEval q z.1.1 z.1.2 = evalMessage q z := by
  unfold messageEval pairEval evalMessage initialP0 initialP1
  rw [naturalCoefficientPolynomial_eval_eq_sum (by decide),
      naturalCoefficientPolynomial_eval_eq_sum (by decide)]
  simp only [evenCoefficients,oddCoefficients]

/-- The same recurrence as basis::double, transported through the embedding. -/
theorem doubled_embed (x : Q) (n : Nat) :
    doubledFactor (embed x) n = embed (doubledFactor x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [doubledFactor,ih]
    simp only [embed,doubledFactor,map_sub,map_mul,map_pow,map_ofNat,map_one]

theorem natural_embed (x : Q) (n : Nat) :
    naturalLineValue (embed x) n = embed (naturalLineValue x n) := by
  unfold naturalLineValue
  simp only [doubled_embed]
  simp only [embed,map_prod]

theorem pair_embed (q : Fin 1024 → Q) (x : Q) :
    pairEval (fun i => embed (q i)) (embed x) =
      (embed (pairEval q x).1,embed (pairEval q x).2) := by
  unfold pairEval
  simp only [natural_embed]
  simp only [embed,map_sum,map_mul]

theorem message_embed (q : Fin 1024 → Q) (x y : Q) :
    messageEval (fun i => embed (q i)) (embed x) (embed y) =
      embed (messageEval q x y) := by
  unfold messageEval
  rw [pair_embed]
  simp only [embed,map_add,map_mul]

theorem message_range (q : Fin 1024 → Q) (x y : Q) :
    InQM (messageEval (fun i => embed (q i)) (embed x) (embed y)) :=
  ⟨messageEval q x y,message_embed q x y⟩

/-- Field-by-field y1 range; lane ordering and number are explicit. No
canonical-value premise, decoder success, or source success is required. -/
def y1 (coefficients : Fin 29 → Fin 1024 → Q) (x y : Q) : Fin 29 → E :=
  fun lane => messageEval (fun i => embed (coefficients lane i)) (embed x) (embed y)

theorem y1_range (coefficients : Fin 29 → Fin 1024 → Q) (x y : Q) (lane : Fin 29) :
    InQM (y1 coefficients x y lane) := message_range _ _ _

theorem y1_decode (coefficients : Fin 29 → Fin 1024 → Q) (x y : Q) (lane : Fin 29) :
    AspisR1.FoldedLeafCodec.decodeWide
      ((List.ofFn (bytes (y1 coefficients x y lane))).map UInt8.toFin) =
        some (y1 coefficients x y lane) := bytes_decode _

theorem y1_compact (coefficients : Fin 29 → Fin 1024 → Q) (x y : Q) (lane : Fin 29)
    (out : ProverCommitPublish43.Bytes) :
    ProverCommitCompact43.cell (bytes (y1 coefficients x y lane)) out =
      .ok (out ++ ProverCommitCompact43.low (bytes (y1 coefficients x y lane))) :=
  range_compact _ (y1_range _ _ _ _) out

#print axioms message_model
#print axioms doubled_embed
#print axioms natural_embed
#print axioms pair_embed
#print axioms message_embed
#print axioms message_range
#print axioms y1_range
#print axioms y1_decode
#print axioms y1_compact
end R1Z.ProverCommitEval47
