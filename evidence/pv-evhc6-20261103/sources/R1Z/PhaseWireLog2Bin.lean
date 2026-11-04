import R1Z.PrivacyR1HeadlineAcct

/-! Canonical logical opening model. Query order is the fixed finite-set list order;
its two normalized batches split at eleven queries. No source identity is
asserted by constructing this model. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseWireLog2Bin
open R0P R0Z.MaskLayout R0Z R0Z.JointView R0Z.FsStatement
  R1Z.EventsR1PBin R1Z.CouplingR1PBin R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.LayoutR1PBin
  R1Z.PrivacyR1Final R1Z.PhaseProtocolInstanceBin
attribute [local instance] Classical.propDecidable
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
attribute [local irreducible] PrivacyR1AcctBasis.basis
  PhaseLeafEncodingBin.c1Leaf PhaseLeafEncodingBin.c2Leaf PhaseLeafEncodingBin.foldedLeaf
  AspisR1.FoldedLeafCodec.encodeFolded q1
variable {CommitHandle Aux : Type}

/-- D88's leaf encoder fixes S2; select that same transport in the view. -/
def honest (h : HonestProver K) : HonestProver K :=
  { h with transport := AspisR1.rowEquiv }

def foldedIndex (u : Fib) : Fib := ⟨u.val / 4, by have := u.isLt; omega⟩
def treeFib (qs : Finset Fib) (T : Fin 3) : Finset Fib :=
  if T.val = 2 then qs.image foldedIndex else qs

def batchQueries (ch : Challenges K) (b : Fin 2) : Finset Fib :=
  (if b.val = 0 then ch.queries.toList.take 11 else ch.queries.toList.drop 11).toFinset

def fib (ch : Challenges K) : Fin 3 → Finset Fib := treeFib ch.queries

def batchFib (ch : Challenges K) (b : Fin 2) : Fin 3 → Finset Fib :=
  treeFib (batchQueries ch b)

/-- Finite-set conversion is symbolic; no large carrier is evaluated. -/
def reads (ch : Challenges K) (b : Fin 2) : List (Fin 3 ⊕ RIdx) :=
  (EventsR1PBin.batchReadSet (batchFib ch b)).toList

def opens (ch : Challenges K) : List (Fin 3 ⊕ RIdx) := reads ch 0 ++ reads ch 1

theorem query_union (ch : Challenges K) :
    batchQueries ch 0 ∪ batchQueries ch 1 = ch.queries := by
  unfold batchQueries
  simp only [Fin.val_zero, Fin.val_one, ite_true, if_neg (by decide : ¬ (1 = 0))]
  rw [← List.toFinset_append, List.take_append_drop, Finset.toList_toFinset]

theorem fibre_union (ch : Challenges K) (T : Fin 3) :
    fib ch T = batchFib ch 0 T ∪ batchFib ch 1 T := by
  unfold fib batchFib treeFib
  split
  · rw [← Finset.image_union, query_union]
  · exact (query_union ch).symm

theorem reads_nodup (ch : Challenges K) (b : Fin 2) : (reads ch b).Nodup :=
  Finset.nodup_toList _

theorem reads_coverage (ch : Challenges K) (b : Fin 2) (c : Fin 3 ⊕ RIdx) :
    c ∈ reads ch b ↔ openedQ (batchFib ch b) c := by
  simp only [reads, Finset.mem_toList, EventsR1PBin.mem_batchReadSet]

/-- Leaf bytes reconstructed from the logical disclosed cells. -/
def viewLeaf (v : View K CommitHandle Aux R1Bat) (T : Fin 3) (u : Fib) : List UInt8 :=
  if T.val = 0 then PhaseLeafEncodingBin.openedC1 v.2 u
  else if T.val = 1 then PhaseLeafEncodingBin.openedC2 v.2 u
  else if hu : u.val < 65536 then (AspisR1.FoldedLeafCodec.encodeFolded (fun s : Fin 4 =>
    v.2 (.bat (.folded ⟨4*u.val+s.val, by omega⟩)))).map UInt8.ofFin
  else List.replicate 128 0

variable (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)

theorem leaf_view (w : (honest h).Instance) (τ : Tape K F) (ch : Challenges K)
    (T : Fin 3) (u : Fib) (hu : u ∈ fib ch T) :
    PhaseLeafConstructionBin.leafVal PhaseLeafEncodingBin.encoding B (honest h) w x τ ch T u =
      viewLeaf (view (honest h) B outputs x w ch τ) T u := by
  rw [PhaseLeafEncodingBin.honest_leaves]
  unfold viewLeaf
  dsimp only [view, R0Z.JointView.payload]
  by_cases h0 : T.val = 0
  · have hq : u ∈ ch.queries := by
      simpa only [fib, treeFib, h0, if_neg (by decide : ¬ (0 = 2))] using hu
    simp only [h0, if_true]
    exact PhaseLeafEncodingBin.c1_view (honest h).transport rfl x.1 B
      (applyEligible ((honest h).build w) τ.2) τ.1 ch u hq
  · by_cases h1 : T.val = 1
    · have hq : u ∈ ch.queries := by
        simpa only [fib, treeFib, h1, if_neg (by decide : ¬ (1 = 2))] using hu
      simp only [h1, if_true]
      exact PhaseLeafEncodingBin.c2_view (honest h).transport rfl x.1 B
        (applyEligible ((honest h).build w) τ.2) τ.1 ch u hq
    · have h2 : T.val = 2 := by omega
      have hm : u ∈ ch.queries.image foldedIndex := by
        simpa only [fib, treeFib, h2, if_true] using hu
      obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hm
      have hv : q.val / 4 = u.val := congrArg Fin.val he
      have hb : u.val < 65536 := by have := q.isLt; omega
      simp only [h0, h1, if_false, dif_pos hb]
      exact PhaseLeafEncodingBin.folded_view (honest h).transport x.1 B
        (applyEligible ((honest h).build w) τ.2) τ.1 ch u hb
        (fun s => ⟨q, hq, by dsimp; omega⟩)

/-- Only roots, disclosed leaves and ancestor nodes are serialized. Their
addresses contain neither private attempt secrets nor the statement digest. -/
def entry (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (c : Fin 3 ⊕ RIdx) : List UInt8 × OracleAnswer :=
  ((match c with
    | .inl T => nodeBytes rest (rootChild T)
    | .inr (.inr (.inr (.inr (.inl (T,u))))) =>
      [0x10, treeTag T] ++ viewLeaf v T u ++ R1Z.LensR1.ans (rest (qSalt T u))
    | .inr (.inr (.inr (.inr (.inr (T,n))))) => nodeBytes rest (childQ T n)
    | _ => []), ansC roots rest c)

def log (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (ch : Challenges K) : List (List UInt8 × OracleAnswer) :=
  (opens ch).map (entry rest roots v)

/-- One source boundary: the Rust ordered verifier read serialization must
be exactly this logical encoding, including ordering, multiplicity and bytes. -/
def RustSerializationJoin
    (rust : (RIdx → OracleAnswer) → (Fin 3 → OracleAnswer) →
      View K CommitHandle Aux R1Bat → Challenges K → List (List UInt8 × OracleAnswer)) : Prop :=
  rust = log


theorem opened_union (a b : Fin 3 → Finset Fib) (c : Fin 3 ⊕ RIdx) :
    openedQ (fun T => a T ∪ b T) c ↔ openedQ a c ∨ openedQ b c := by
  rcases c with T | (b' | i | ⟨T,u⟩ | ⟨T,u⟩ | ⟨T,n⟩)
  · simp only [openedQ, true_or]
  · simp only [openedQ, false_or]
  · simp only [openedQ, false_or]
  · simp only [openedQ, false_or]
  · exact Finset.mem_union
  · simp only [openedQ, Finset.mem_union]
    constructor
    · rintro ⟨u, hu | hu, he⟩
      · exact Or.inl ⟨u, hu, he⟩
      · exact Or.inr ⟨u, hu, he⟩
    · rintro (⟨u, hu, he⟩ | ⟨u, hu, he⟩)
      · exact ⟨u, Or.inl hu, he⟩
      · exact ⟨u, Or.inr hu, he⟩

theorem opens_coverage (ch : Challenges K) (c : Fin 3 ⊕ RIdx) :
    c ∈ opens ch ↔ openedQ (fib ch) c := by
  rw [opens, List.mem_append, reads_coverage, reads_coverage]
  have he : fib ch = fun T => batchFib ch 0 T ∪ batchFib ch 1 T :=
    funext (fibre_union ch)
  rw [he, opened_union]

theorem entry_grammar (w : (honest h).Instance) (τ : Tape K F) (ch : Challenges K)
    (pub : List UInt8) (tag : UInt8) (sec : SecP) (d : OracleAnswer)
    (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer)
    (c : Fin 3 ⊕ RIdx) (hc : openedQ (fib ch) c) :
    entry rest roots (view (honest h) B outputs x w ch τ) c =
      (gram pub tag (PhaseLeafConstructionBin.leafVal PhaseLeafEncodingBin.encoding B
        (honest h) w x τ ch) sec d rest
          (cposOf (E₁ := PrivacyR1AcctModel.E₁) (E₂ := PrivacyR1AcctModel.E₂) c),
        ansC roots rest c) := by
  rcases c with T | (b | i | ⟨T,u⟩ | ⟨T,u⟩ | ⟨T,n⟩)
  · rfl
  · exact False.elim hc
  · exact False.elim hc
  · exact False.elim hc
  · simp only [entry, cposOf, gram]
    rw [leaf_view h outputs x w τ ch T u hc]
  · rfl

variable (template : R1Wire K CommitHandle Aux)
local notation "base" => PrivacyR1AcctModel.base template log
local notation "W" => PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) (honest h) B outputs x)
variable (decode : (Fin PrivacyR1AcctModel.E₁ → OracleAnswer) →
  (Fin PrivacyR1AcctModel.E₂ → OracleAnswer) → Option (Tape K F))
local notation "seed" => PrivacyR1AcctModel.seed W decode fib opens
local notation "Pr" => PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) (honest h) B outputs x seed)

def batches : RWireBatches W Pr where
  fib := batchFib
  reads := reads
  concatenation := fun _ => rfl
  nodup := reads_nodup
  coverage := reads_coverage
  fibre_union := fibre_union

theorem ordered_log (w : (honest h).Instance) (sec : SecP) (d : OracleAnswer)
    (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer)
    (ch : Challenges K) :
    R1Wire.comLog W ((PrivacyR1AcctModel.wire_coins template log (honest h) outputs x).symm rest)
      roots (view (honest h) B outputs x w ch τ) ch =
    (R1ProverP.openList Pr ch).map (fun c =>
      (gram (R1Wire.pubBytes W x) (R1Wire.vtag W) (R1ProverP.leafVal Pr (honest h) w x τ ch) sec d rest
        (cposOf (E₁ := (R1ProverP.E₁ Pr)) (E₂ := (R1ProverP.E₂ Pr)) c), ansC roots rest c)) := by
  change (opens ch).map _ = (opens ch).map _
  apply List.map_congr_left
  intro c hc
  exact entry_grammar h outputs x w τ ch _ _ sec d roots rest c
    ((opens_coverage ch c).mp hc)

#print axioms opened_union
#print axioms opens_coverage
#print axioms entry_grammar
#print axioms batches
#print axioms ordered_log

#print axioms query_union
#print axioms fibre_union
#print axioms reads_nodup
#print axioms reads_coverage
#print axioms leaf_view
end R1Z.PhaseWireLog2Bin
