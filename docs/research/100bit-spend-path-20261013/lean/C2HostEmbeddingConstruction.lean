import C2HostEmbedding

/-! Bind the checked actual embedding primitive into the conditional owner
model. This does not bind Backend::c2 or Commitment::build execution: those
source-refinement obligations and encoder/transport/length/custody boundaries
remain open. -/
set_option autoImplicit false
namespace AspisR1.C2HostEmbeddingConstruction.Core

/- The generic construction core is deliberately isolated from every historical
LiteralSemanticPrefix/RawCut/FS2/Circle import. Its code is the earlier generic
core with only the enclosing namespace changed; this file checks it anew under
just the audited current embedding/Aeneas dependency closure. -/
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

#print axioms run_of_steps
#print axioms steps_of_run
#print axioms copied_rows_of_run
#print axioms encoder_returns_of_run
#print axioms first_encoder_error
#print axioms second_encoder_error
end AspisR1.C2HostEmbeddingConstruction.Core

namespace AspisR1.C2HostEmbeddingConstruction
open Aeneas Aeneas.Std Result
open AspisC2HostEmbedding
open Core

variable {Variant Error Tree : Type}

/-- Only embed/project are instantiated here. All other operations stay
explicit; no output is inferred from their signatures. -/
def operations
    (transport : Variant → Rows field.wide_exact.WideExact → Rows field.wide_exact.WideExact)
    (check : Rows field.wide_exact.WideExact → Except Error Unit)
    (encode : Rows field.QM31 → Except Error (List field.QM31))
    (tree : List field.QM31 → List field.QM31 → Except Error Tree) :
    Operations field.QM31 field.wide_exact.WideExact Variant Error Tree where
  embed := C2HostEmbedding.embed
  project := fun x => x.c0
  coefficients := transport
  checkField := check
  encode := encode
  buildTree := tree

/-- Every element of the copied input is the exact successful result of the
actual extracted WideExact constructor, including its canonicalization. -/
theorem copied_element
    (transport : Variant → Rows field.wide_exact.WideExact → Rows field.wide_exact.WideExact)
    (check : Rows field.wide_exact.WideExact → Except Error Unit)
    (encode : Rows field.QM31 → Except Error (List field.QM31))
    (tree : List field.QM31 → List field.QM31 → Except Error Tree)
    (rows : Rows field.QM31) (r : Fin 1024) :
    field.wide_exact.WideExact.from_qm31 (rows r) =
      ok (copied (operations transport check encode tree) rows r) :=
  C2HostEmbedding.embed_success (rows r)

/-- An output retained by successful conditional construction has the actual
per-element embedding results. The premise is the model run; actual Rust loop
reachability/owner refinement has not been supplied. -/
theorem retained_elements_of_run
    (transport : Variant → Rows field.wide_exact.WideExact → Rows field.wide_exact.WideExact)
    (check : Rows field.wide_exact.WideExact → Except Error Unit)
    (encode : Rows field.QM31 → Except Error (List field.QM31))
    (tree : List field.QM31 → List field.QM31 → Except Error Tree)
    (variant : Variant) (h1 g : Rows field.QM31)
    (owner : Owned field.QM31 field.wide_exact.WideExact Tree)
    (hrun : run (operations transport check encode tree) variant h1 g = .ok owner)
    (r : Fin 1024) :
    field.wide_exact.WideExact.from_qm31 (h1 r) = ok (owner.savedH1 r) ∧
    field.wide_exact.WideExact.from_qm31 (g r) = ok (owner.savedG r) := by
  obtain ⟨hh, hg⟩ := copied_rows_of_run
    (operations transport check encode tree) variant h1 g owner hrun
  rw [hh, hg]
  exact ⟨copied_element transport check encode tree h1 r,
    copied_element transport check encode tree g r⟩

#print axioms copied_element
#print axioms retained_elements_of_run
end AspisR1.C2HostEmbeddingConstruction
