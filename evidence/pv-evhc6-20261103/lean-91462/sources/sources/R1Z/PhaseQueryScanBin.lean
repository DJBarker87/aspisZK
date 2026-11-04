import R1Z.PhaseLocalityBin

/-! An eight-block first-completion scan. Readiness and query decoding get
only the observed observed and its endpoint. The concrete word parser and
22-distinct readiness predicate are source parameters, not silently assumed
to have been identified with Rust. Only the eight block indices are finite. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseQueryScanBin
open R0Z.FsStatement R1Z.GamesR1PBin
attribute [local instance] Classical.propDecidable

def PrefixAgree (q q' : Fin 8 → OracleAnswer) (k : Fin 8) : Prop :=
  ∀ j, j ≤ k → q j = q' j

def observed (q : Fin 8 → OracleAnswer) (k : Fin 8) : Fin 8 → OracleAnswer :=
  fun j => if j ≤ k then q j else 0

theorem prefix_eq (q q' : Fin 8 → OracleAnswer) (k : Fin 8)
    (he : PrefixAgree q q' k) : observed q k = observed q' k := by
  funext j
  unfold observed
  split
  · exact he j (by assumption)
  · rfl

def candidates (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q : Fin 8 → OracleAnswer) : Finset (Fin 8) :=
  Finset.univ.filter (fun k => done k (observed q k) ∨ k = 7)

theorem candidates_nonempty (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q : Fin 8 → OracleAnswer) : (candidates done q).Nonempty := by
  exact ⟨7, by simp [candidates]⟩

def stop (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q : Fin 8 → OracleAnswer) : Fin 8 :=
  (candidates done q).min' (candidates_nonempty done q)

theorem stop_mem (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q : Fin 8 → OracleAnswer) : stop done q ∈ candidates done q :=
  Finset.min'_mem _ _

theorem stop_le (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q : Fin 8 → OracleAnswer) (k : Fin 8) (hk : k ∈ candidates done q) :
    stop done q ≤ k := Finset.min'_le _ k hk

theorem candidates_agree (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q q' : Fin 8 → OracleAnswer) (k b : Fin 8)
    (he : PrefixAgree q q' b) (hk : k ≤ b) :
    k ∈ candidates done q ↔ k ∈ candidates done q' := by
  have hp : observed q k = observed q' k := prefix_eq q q' k (fun j hj => he j (hj.trans hk))
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and, hp]

/-- Selection cannot inspect a block after its own stopping point, including
the exhaustion/default case k=7. -/
theorem stop_local (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (q q' : Fin 8 → OracleAnswer) (he : PrefixAgree q q' (stop done q)) :
    stop done q = stop done q' := by
  have hb : stop done q' ≤ stop done q := stop_le done q' _
    ((candidates_agree done q q' _ _ he le_rfl).mp (stop_mem done q))
  have ha : stop done q ≤ stop done q' := stop_le done q _
    ((candidates_agree done q q' _ _ he hb).mpr (stop_mem done q'))
  exact le_antisymm ha hb

def queries (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (decode : Fin 8 → (Fin 8 → OracleAnswer) → Finset Fib)
    (q : Fin 8 → OracleAnswer) : Finset Fib :=
  decode (stop done q) (observed q (stop done q))

theorem queries_local (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (decode : Fin 8 → (Fin 8 → OracleAnswer) → Finset Fib)
    (q q' : Fin 8 → OracleAnswer) (he : PrefixAgree q q' (stop done q)) :
    queries done decode q = queries done decode q' := by
  have hs := stop_local done q q' he
  have hp := prefix_eq q q' (stop done q) he
  unfold queries
  rw [← hs, hp]

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Install the constructed block decoder and first-completion scan in a
wire's remaining data. Message locality must still be proved for this wire. -/
def wireData (W : R1Z.GamesR1.R1Wire K CommitHandle Aux)
    (scalar : OracleAnswer → K)
    (circle : Fin 2 → OracleAnswer → AspisR0.ChordGeometry.Point K)
    (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (decode : Fin 8 → (Fin 8 → OracleAnswer) → Finset Fib) :
    R1Z.GamesR1.R1Wire K CommitHandle Aux :=
  { W with
    dec := R1Z.PhaseLocalityBin.phaseDecode scalar circle (queries done decode)
    kstarOf := stop done }

theorem wireData_decoder_local (W : R1Z.GamesR1.R1Wire K CommitHandle Aux)
    (scalar : OracleAnswer → K)
    (circle : Fin 2 → OracleAnswer → AspisR0.ChordGeometry.Point K)
    (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (decode : Fin 8 → (Fin 8 → OracleAnswer) → Finset Fib) :
    R1Z.PhaseLocalityBin.DecodeLocal (wireData W scalar circle done decode).dec :=
  R1Z.PhaseLocalityBin.phaseDecode_local scalar circle (queries done decode)

theorem wireData_scan_local (W : R1Z.GamesR1.R1Wire K CommitHandle Aux)
    (scalar : OracleAnswer → K)
    (circle : Fin 2 → OracleAnswer → AspisR0.ChordGeometry.Point K)
    (done : Fin 8 → (Fin 8 → OracleAnswer) → Prop)
    (decode : Fin 8 → (Fin 8 → OracleAnswer) → Finset Fib)
    (q q' : Fin 8 → OracleAnswer)
    (he : PrefixAgree q q' ((wireData W scalar circle done decode).kstarOf q)) :
    (wireData W scalar circle done decode).kstarOf q =
      (wireData W scalar circle done decode).kstarOf q' ∧
    queries done decode q = queries done decode q' :=
  ⟨stop_local done q q' he, queries_local done decode q q' he⟩

#print axioms wireData_decoder_local
#print axioms wireData_scan_local
#print axioms prefix_eq
#print axioms candidates_nonempty
#print axioms stop_mem
#print axioms stop_le
#print axioms candidates_agree
#print axioms stop_local
#print axioms queries_local
end R1Z.PhaseQueryScanBin
