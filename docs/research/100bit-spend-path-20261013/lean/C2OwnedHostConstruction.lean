import R1LiteralSemanticPrefix

/-!
Conditional construction component for the known-host C2 path.

This is a small functional model of the C2 lane portion of
`host_commitment::Commitment::build`, NOT a checked translation of that Rust
function or of `Backend::c2`. The exact caller/build extraction attempts and
remaining source-refinement obligations are recorded alongside this file.

The inputs are owned H1/G rows. Embedding, variant coefficient transport,
field validation, encoding and final tree construction are explicit operations.
No assumption says the output already owns a desired word. Successful execution
produces the retained vectors, from which the literal word is constructed.
The length checks used to form a finite literal word are explicit premises;
the encoder's return type alone gives no length or content guarantee.
Packing, salts/path custody, transcript execution and checkpoint authentication
are separate obligations. In particular no root or sampler value recovers the
word here, and no zero-C2 placeholder is used.
-/
set_option autoImplicit false

namespace AspisR1.C2OwnedHostConstruction

abbrev Rows (K : Type) := Fin 1024 → K

structure Operations (K W Variant Error Tree : Type) where
  embed : K → W
  project : W → K
  coefficients : Variant → Rows W → Rows W
  checkField : Rows W → Except Error Unit
  encode : Rows K → Except Error (List K)
  buildTree : List K → List K → Except Error Tree

structure Owned (K W Tree : Type) where
  savedH1 : Rows W
  savedG : Rows W
  encodedH1 : List K
  encodedG : List K
  tree : Tree

variable {K W Variant Error Tree : Type}

def copied (ops : Operations K W Variant Error Tree) (rows : Rows K) : Rows W :=
  fun r => ops.embed (rows r)

def coefficients (ops : Operations K W Variant Error Tree)
    (variant : Variant) (rows : Rows K) : Rows K :=
  fun r => ops.project (ops.coefficients variant (copied ops rows) r)

/-- The two C2 iterations, in their source order. `buildTree` is the explicit
remaining packing/hash/tree boundary. The model does not specify its result. -/
def run (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) : Except Error (Owned K W Tree) :=
  match ops.checkField (copied ops h1) with
  | .error e => .error e
  | .ok () =>
    match ops.encode (coefficients ops variant h1) with
    | .error e => .error e
    | .ok wh =>
      match ops.checkField (copied ops g) with
      | .error e => .error e
      | .ok () =>
        match ops.encode (coefficients ops variant g) with
        | .error e => .error e
        | .ok wg =>
          match ops.buildTree wh wg with
          | .error e => .error e
          | .ok tree => .ok ⟨copied ops h1, copied ops g, wh, wg, tree⟩

/-- Primitive successes produce the retained owner. These are individual
operation outcomes, not a premise equating final metadata to a desired word. -/
theorem run_of_steps (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) (wh wg : List K) (tree : Tree)
    (hh : ops.checkField (copied ops h1) = .ok ())
    (hw : ops.encode (coefficients ops variant h1) = .ok wh)
    (hg : ops.checkField (copied ops g) = .ok ())
    (gw : ops.encode (coefficients ops variant g) = .ok wg)
    (ht : ops.buildTree wh wg = .ok tree) :
    run ops variant h1 g =
      .ok ⟨copied ops h1, copied ops g, wh, wg, tree⟩ := by
  simp [run, hh, hw, hg, gw, ht]

/-- Inverting a successful construction exposes the exact individual encoder
returns and the stored vectors, instead of postulating their contents. -/
theorem steps_of_run (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) (owner : Owned K W Tree)
    (hrun : run ops variant h1 g = .ok owner) :
    ∃ wh wg tree,
      ops.checkField (copied ops h1) = .ok () ∧
      ops.encode (coefficients ops variant h1) = .ok wh ∧
      ops.checkField (copied ops g) = .ok () ∧
      ops.encode (coefficients ops variant g) = .ok wg ∧
      ops.buildTree wh wg = .ok tree ∧
      owner = ⟨copied ops h1, copied ops g, wh, wg, tree⟩ := by
  cases hh : ops.checkField (copied ops h1) with
  | error e => simp [run, hh] at hrun
  | ok u =>
    cases u
    cases hw : ops.encode (coefficients ops variant h1) with
    | error e => simp [run, hh, hw] at hrun
    | ok wh =>
      cases hg : ops.checkField (copied ops g) with
      | error e => simp [run, hh, hw, hg] at hrun
      | ok u =>
        cases u
        cases gw : ops.encode (coefficients ops variant g) with
        | error e => simp [run, hh, hw, hg, gw] at hrun
        | ok wg =>
          cases ht : ops.buildTree wh wg with
          | error e => simp [run, hh, hw, hg, gw, ht] at hrun
          | ok tree =>
            have ho : (⟨copied ops h1, copied ops g, wh, wg, tree⟩ : Owned K W Tree) = owner := by
              simpa [run, hh, hw, hg, gw, ht] using hrun
            exact ⟨wh, wg, tree, rfl, rfl, rfl, rfl, ht, ho.symm⟩

theorem copied_rows_of_run (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) (owner : Owned K W Tree)
    (hrun : run ops variant h1 g = .ok owner) :
    owner.savedH1 = copied ops h1 ∧ owner.savedG = copied ops g := by
  obtain ⟨wh, wg, tree, _, _, _, _, _, ho⟩ := steps_of_run ops variant h1 g owner hrun
  subst owner
  exact ⟨rfl, rfl⟩

theorem encoder_returns_of_run (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) (owner : Owned K W Tree)
    (hrun : run ops variant h1 g = .ok owner) :
    ops.encode (coefficients ops variant h1) = .ok owner.encodedH1 ∧
    ops.encode (coefficients ops variant g) = .ok owner.encodedG := by
  obtain ⟨wh, wg, tree, _, hw, _, gw, _, ho⟩ := steps_of_run ops variant h1 g owner hrun
  subst owner
  exact ⟨hw, gw⟩

/-- A real failure of the first encoder prevents validation/encoding of G
and tree construction in this sequential functional model. -/
theorem first_encoder_error (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) (e : Error)
    (hh : ops.checkField (copied ops h1) = .ok ())
    (hw : ops.encode (coefficients ops variant h1) = .error e) :
    run ops variant h1 g = .error e := by
  simp [run, hh, hw]

theorem second_encoder_error (ops : Operations K W Variant Error Tree)
    (variant : Variant) (h1 g : Rows K) (wh : List K) (e : Error)
    (hh : ops.checkField (copied ops h1) = .ok ())
    (hw : ops.encode (coefficients ops variant h1) = .ok wh)
    (hg : ops.checkField (copied ops g) = .ok ())
    (gw : ops.encode (coefficients ops variant g) = .error e) :
    run ops variant h1 g = .error e := by
  simp [run, hh, hw, hg, gw]

open ExactLeafFieldCodec

/-- Interpret the retained raw vectors only after checking their actual
lengths. `toExact` is an explicit raw-field interpretation boundary. -/
def word (toExact : K → QM31Exact) (owner : Owned K W Tree)
    (hh : owner.encodedH1.length = 1048576)
    (hg : owner.encodedG.length = 1048576) : LiteralTypedWords.C2Word :=
  fun i j => if j.val = 0 then
    toExact (owner.encodedH1[i.val]'(by rw [hh]; exact i.isLt))
  else
    toExact (owner.encodedG[i.val]'(by rw [hg]; exact i.isLt))

theorem word_first (toExact : K → QM31Exact) (owner : Owned K W Tree)
    (hh : owner.encodedH1.length = 1048576)
    (hg : owner.encodedG.length = 1048576) (i : Fin 1048576) :
    word toExact owner hh hg i 0 =
      toExact (owner.encodedH1[i.val]'(by rw [hh]; exact i.isLt)) := by
  simp [word]

theorem word_second (toExact : K → QM31Exact) (owner : Owned K W Tree)
    (hh : owner.encodedH1.length = 1048576)
    (hg : owner.encodedG.length = 1048576) (i : Fin 1048576) :
    word toExact owner hh hg i 1 =
      toExact (owner.encodedG[i.val]'(by rw [hg]; exact i.isLt)) := by
  simp [word]

/-- Row-2 auxiliary metadata comes from the retained vectors. Bytes are an
independent argument; this constructor does not prove they encode `owner.tree`. -/
def literalMessage (bytes : LiteralTranscript.BytesMessage)
    (toExact : K → QM31Exact) (owner : Owned K W Tree)
    (hh : owner.encodedH1.length = 1048576)
    (hg : owner.encodedG.length = 1048576) : LiteralTranscript.Message :=
  .c2 bytes (word toExact owner hh hg)

/-- The semantic callback selects the two owned encoder results, index for
index. No root, hash, sampler, or zero-word argument appears. -/
theorem semantic_pair (toExact : K → QM31Exact) (owner : Owned K W Tree)
    (hh : owner.encodedH1.length = 1048576)
    (hg : owner.encodedG.length = 1048576)
    (eK : QM31Exact →+* LiteralSemanticPrefix.E) (i : Fin 1048576) :
    (LiteralSemanticPrefix.c2Pair eK (word toExact owner hh hg)).1 i =
      eK (toExact (owner.encodedH1[i.val]'(by rw [hh]; exact i.isLt))) ∧
    (LiteralSemanticPrefix.c2Pair eK (word toExact owner hh hg)).2 i =
      eK (toExact (owner.encodedG[i.val]'(by rw [hg]; exact i.isLt))) := by
  simp [LiteralSemanticPrefix.c2Pair, word]

#print axioms run_of_steps
#print axioms steps_of_run
#print axioms copied_rows_of_run
#print axioms encoder_returns_of_run
#print axioms first_encoder_error
#print axioms second_encoder_error
#print axioms word_first
#print axioms word_second
#print axioms semantic_pair

end AspisR1.C2OwnedHostConstruction
