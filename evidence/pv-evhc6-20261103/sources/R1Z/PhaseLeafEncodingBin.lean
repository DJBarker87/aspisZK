import R1Z.PhaseLeafConstructionBin
import R1Z.PhaseMessageEncodingBin
import R1Z.BuilderTransport

/-! Exact-wide Lean-model leaf encoding: D18/S2 row transport, the existing
circle/line domain evaluators, fibre-major lane selection, retained byte
serialization, and folded-tree zero padding. No FFT/Rust execution identity
or low-subfield guard is inferred from these mathematical definitions. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseLeafEncodingBin
open R0P R0P.SemSource R0Z R0Z.HonestView R0Z.MaskLayout R0Z.JointView
  R1Z.Batched R1Z.GamesR1PBin R1Z.PhaseBuilderDependenciesBin
  R1Z.PhaseMessageEncodingBin AspisPool.AlgorithmicCircleDecoderV7

abbrev K := AspisWideTower.WideExact

/-- The original model reads coefficients through pi.symm. D18 is involutive. -/
def coefficients (m : Fin 1024 → K) : Fin 1024 → K := coeffsLinear AspisR1.rowEquiv m

theorem s2_coefficient (m : Fin 1024 → K) (j : Fin 1024) :
    coefficients m j = m (AspisR1.row j) := rfl

/-- Connect the selected coefficient index to the extracted S2 reference. -/
theorem extracted_s2_index (j : Aeneas.Std.Usize) (hj : j.val < 1024) :
    ∃ out : Aeneas.Std.Usize, ∃ hout : out.val < 1024,
      AspisBuilderReference.row_arithmetic j = .ok out ∧
      ∀ m : Fin 1024 → K, coefficients m ⟨j.val, hj⟩ = m ⟨out.val, hout⟩ := by
  obtain ⟨out, ho, hv⟩ := R1Z.BuilderTransport.reference_row_fin j hj
  have hout : out.val < 1024 := by
    rw [hv]
    exact (AspisR1.row ⟨j.val, hj⟩).isLt
  refine ⟨out, hout, ho, ?_⟩
  intro m
  rw [s2_coefficient]
  congr 1
  exact Fin.ext hv.symm

/-- Both commitments store four successive domain symbols, slot then lane. -/
def initialSymbol (m : Fin 1024 → K) (u : Fib) (s : Fin 4) : K :=
  AspisWide.InitialEncoder.exactInitialEncoder (coefficients m) (AspisV5ComponentCConcreteFoldLinearity.childIndex u s)

def c1Leaf (t : Trace K) (u : Fib) : List UInt8 :=
  (List.ofFn (fun s : Fin 4 =>
    (List.ofFn (fun c : Fin 27 =>
      (wideBytes (initialSymbol (t (c1Column c)) u s)).take
        (if c.val < 26 then 4 else 16))).flatten)).flatten

def c2Leaf (t : Trace K) (u : Fib) : List UInt8 :=
  (List.ofFn (fun s : Fin 4 =>
    (List.ofFn (fun c : Fin 2 =>
      (wideBytes (initialSymbol (t ⟨26+c.val, by omega⟩) u s)).take 16)).flatten)).flatten

/-- The final evaluator has 2^18 symbols, hence 2^16 four-symbol data leaves.
The commitment still has 2^18 leaves; the remaining ones are 128 zero bytes. -/
def foldedLeaf (m : Fin 256 → K) (u : Fib) : List UInt8 :=
  if hu : u.val < 65536 then
    (AspisR1.FoldedLeafCodec.encodeFolded (fun s : Fin 4 =>
      AspisWide.FinalEncoder.exactFinalLinear m ⟨4*u.val+s.val, by omega⟩)).map UInt8.ofFin
  else List.replicate 128 0

/-- All three encoder parameters are now instantiated. -/
def encoding : PhaseLeafConstructionBin.LeafEncoding K where
  c1 := fun m u =>
    (List.ofFn (fun s : Fin 4 =>
      (List.ofFn (fun c : Fin 27 =>
        (wideBytes (initialSymbol (m c) u s)).take
          (if c.val < 26 then 4 else 16))).flatten)).flatten
  c2 := fun m u =>
    (List.ofFn (fun s : Fin 4 =>
      (List.ofFn (fun c : Fin 2 =>
        (wideBytes (initialSymbol (m c) u s)).take 16)).flatten)).flatten
  folded := foldedLeaf

attribute [local irreducible] initialSymbol wideBytes
  c1Leaf c2Leaf foldedLeaf

theorem encoding_c1 (t : Trace K) (u : Fib) :
    encoding.c1 (fun c => t (c1Column c)) u = c1Leaf t u := by
  unfold encoding c1Leaf
  rfl

theorem encoding_c2 (t : Trace K) (u : Fib) :
    encoding.c2 (fun c => t ⟨26+c.val, by omega⟩) u = c2Leaf t u := by
  unfold encoding c2Leaf
  rfl

theorem folded_padding (m : Fin 256 → K) (u : Fib) (hu : 65536 ≤ u.val) :
    encoding.folded m u = List.replicate 128 0 := by
  unfold encoding foldedLeaf
  exact dif_neg (by omega)

theorem folded_data (m : Fin 256 → K) (u : Fib) (hu : u.val < 65536) :
    encoding.folded m u =
      (AspisR1.FoldedLeafCodec.encodeFolded (fun s : Fin 4 =>
        AspisWide.FinalEncoder.exactFinalLinear m ⟨4*u.val+s.val, by omega⟩)).map UInt8.ofFin := by
  unfold encoding foldedLeaf
  exact dif_pos hu

/-- Equality with the three independently named model leaves on the same
prepared, masked honest trace. C1's preparation is removed by its dependency
lemma; C2 selects 26/27; folded consumes the existing Batched.q1 word. -/
theorem honest_leaves {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (h : HonestProver K) (w : h.Instance)
    (x : Statement K CommitHandle) (τ : Tape K F) (ch : R0Z.HonestView.Challenges K) (T : Fin 3) (u : Fib) :
    PhaseLeafConstructionBin.leafVal encoding B h w x τ ch T u =
      let t := applyAff B (prepare x.1 (applyEligible (h.build w) τ.2) ch) τ.1
      if T.val = 0 then c1Leaf t u
      else if T.val = 1 then c2Leaf t u
      else foldedLeaf (q1 h.transport ch t) u := by
  dsimp only
  unfold PhaseLeafConstructionBin.leafVal
  split
  · change encoding.c1 _ u = c1Leaf _ u
    rw [← encoding_c1]
    apply congrArg (fun cols => encoding.c1 cols u)
    funext c
    exact (c1_challenge_free x.1 (h.build w) B τ ch c).symm
  · split
    · exact encoding_c2 _ u
    · rfl

/-- Serialized source lanes read from the existing query-gated view. -/
def openedC1 (p : R0Z.HonestView.Payload K R1Bat) (u : Fib) : List UInt8 :=
  (List.ofFn (fun s : Fin 4 =>
    (List.ofFn (fun c : Fin 27 =>
      (wideBytes (p (.opened u s (c1Column c)))).take
        (if c.val < 26 then 4 else 16))).flatten)).flatten

def openedC2 (p : R0Z.HonestView.Payload K R1Bat) (u : Fib) : List UInt8 :=
  (List.ofFn (fun s : Fin 4 =>
    (List.ofFn (fun c : Fin 2 =>
      (wideBytes (p (.opened u s ⟨26+c.val, by omega⟩))).take 16)).flatten)).flatten

theorem initialSymbol_run (π : Fin 1024 ≃ Fin 1024) (hπ : π = AspisR1.rowEquiv)
    {F : Subfield K} (pub : Public K) (B : PackBasis F) (t : Trace K)
    (r : AffTape K F) (ch : R0Z.HonestView.Challenges K) (u : Fib) (hu : u ∈ ch.queries)
    (slot : Fin 4) (c : Fin 29) :
    initialSymbol (applyAff B (prepare pub t ch) r c) u slot =
      run (Bat := R1Bat) π pub B t ch r (.opened u slot c) := by
  subst hπ
  simp only [initialSymbol, run, if_pos hu]
  rfl

/-- On queried fibres the instantiated C1/C2 leaves equal the actual disclosed
HonestView cells, with the source's slot/lane order and byte widths. -/
theorem c1_view {F : Subfield K} (π : Fin 1024 ≃ Fin 1024) (hπ : π = AspisR1.rowEquiv)
    (pub : Public K) (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch : R0Z.HonestView.Challenges K) (u : Fib) (hu : u ∈ ch.queries) :
    c1Leaf (applyAff B (prepare pub t ch) r) u =
      openedC1 (run (Bat := R1Bat) π pub B t ch r) u := by
  unfold c1Leaf openedC1
  simp only [initialSymbol_run π hπ pub B t r ch u hu]

theorem c2_view {F : Subfield K} (π : Fin 1024 ≃ Fin 1024) (hπ : π = AspisR1.rowEquiv)
    (pub : Public K) (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch : R0Z.HonestView.Challenges K) (u : Fib) (hu : u ∈ ch.queries) :
    c2Leaf (applyAff B (prepare pub t ch) r) u =
      openedC2 (run (Bat := R1Bat) π pub B t ch r) u := by
  unfold c2Leaf openedC2
  simp only [initialSymbol_run π hπ pub B t r ch u hu]

theorem folded_view {F : Subfield K} (π : Fin 1024 ≃ Fin 1024)
    (pub : Public K) (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch : R0Z.HonestView.Challenges K) (u : Fib) (hu : u.val < 65536)
    (hq : ∀ slot : Fin 4, FoldedOpen ch ⟨4*u.val+slot.val, by omega⟩) :
    foldedLeaf (q1 π ch (applyAff B (prepare pub t ch) r)) u =
      (AspisR1.FoldedLeafCodec.encodeFolded (fun slot : Fin 4 =>
        run (Bat := R1Bat) π pub B t ch r
          (.bat (.folded ⟨4*u.val+slot.val, by omega⟩)))).map UInt8.ofFin := by
  unfold foldedLeaf
  rw [dif_pos hu]
  apply congrArg (fun values => (AspisR1.FoldedLeafCodec.encodeFolded values).map UInt8.ofFin)
  funext slot
  simp only [run]
  exact (read_folded π ch _ _ (hq slot)).symm

#print axioms folded_view
#print axioms initialSymbol_run
#print axioms c1_view
#print axioms c2_view
#print axioms s2_coefficient
#print axioms extracted_s2_index
#print axioms encoding_c1
#print axioms encoding_c2
#print axioms folded_padding
#print axioms folded_data
#print axioms honest_leaves
end R1Z.PhaseLeafEncodingBin
