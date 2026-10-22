import R1Z.ProverCommitMaterialTransport16
import R1Z.ProverCommitMaterialSupport
import AspisR1ProverBalance9.Funs
/-! Assembly of the existing extracted owned components with retained state.
This reference begins after nonce reservation/seed derivation and allocation;
it is not a refinement certificate for the shipped outer builder. -/
set_option autoImplicit false
namespace R1Z.ProverCommitReturned16
open Aeneas Aeneas.Std Result AspisR1ProverMaterial14
open R1Z.ProverCommitMaterialRecursion (Hash State Values QValues)
open R1Z.ProverCommitMaterialSupport
abbrev Error := state_only_hiding.StateOnlyMaskBuildError

/-- Field-preserving transport between the independently extracted types. -/
def toBalance (q : aspis_core.field.QM31) : AspisR1ProverBalance9.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def fromBalance (q : AspisR1ProverBalance9.aspis_core.field.QM31) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def mapVec {α β : Type} (f : α → β) (v : alloc.vec.Vec α) : alloc.vec.Vec β :=
  ⟨v.val.map f, by simpa only [List.length_map] using v.property⟩

theorem field_roundtrip (q : aspis_core.field.QM31) : fromBalance (toBalance q) = q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

theorem vector_roundtrip (v : QValues) :
    mapVec fromBalance (mapVec toBalance v) = v := by
  apply Subtype.ext
  simp only [mapVec, List.map_map]
  change v.val.map (fun q => fromBalance (toBalance q)) = v.val
  simp only [field_roundtrip]
  exact List.map_id v.val

def balanceError : AspisR1ProverBalance9.state_only_hiding.StateOnlyMaskBuildError → Error
  | .ZeroPrivateEntropy => .ZeroPrivateEntropy
  | .ReusedMaskNonce => .ReusedMaskNonce
  | .MaskSampleExhausted => .MaskSampleExhausted
  | .TraceShape => .TraceShape
  | .Layout => .Layout

def balance (values : QValues) (dependent : Usize) (active : Array Bool 1024#usize) :
    Result (core.result.Result Unit Error × QValues) := do
  let (status, values) ← AspisR1ProverBalance9.prover_commit_reference.balance_qm31_owned
    (mapVec toBalance values) dependent active
  let status := match status with
    | .Ok () => .Ok ()
    | .Err e => .Err (balanceError e)
  ok (status, mapVec fromBalance values)

structure ReturnedMaterial where
  c1 : Values
  mask_only_c1 : alloc.vec.Vec Values
  g : QValues
  h1_padding : QValues
  mask_nonce : Array U8 32#usize

/-- Owned assembly, in the source's order. Supplied buffers expose allocation
and capacity responsibilities instead of silently assuming them. Partial
material is not returned on any error; the retained expander state is. -/
def assemble (hash : Hash) (domain : Slice U8) (state : State)
    (cells : Usize) (c1 : Values) (columns : alloc.vec.Vec Values)
    (g padding : QValues) (dependent : Usize) (active : Array Bool 1024#usize)
    (nonce : Array U8 32#usize) :
    Result (core.result.Result ReturnedMaterial Error × State) := do
  let (status, c1, afterC1) ←
    prover_commit_reference.collect_m31_owned hash domain state cells c1
  match status with
  | .Err e => ok (.Err e, afterC1)
  | .Ok () =>
    let (status, columns, afterColumns) ←
      prover_commit_reference.material_columns_owned hash domain afterC1 columns
        0#usize 10#usize dependent active
    match status with
    | .Err e => ok (.Err e, afterColumns)
    | .Ok () =>
      let (status, g, afterG) ←
        prover_commit_reference.collect_qm31_owned hash domain afterColumns 1024#usize g
      match status with
      | .Err e => ok (.Err e, afterG)
      | .Ok () =>
        let (status, g) ← balance g dependent active
        match status with
        | .Err e => ok (.Err e, afterG)
        | .Ok () =>
          let (status, padding, final) ←
            prover_commit_reference.material_padding_owned hash domain afterG padding
              0#usize dependent active
          match status with
          | .Err e => ok (.Err e, final)
          | .Ok () =>
            let (status, padding) ←
              balance padding dependent active
            match status with
            | .Err e => ok (.Err e, final)
            | .Ok () => ok (.Ok ⟨c1, columns, g, padding, nonce⟩, final)

theorem qm_raw_collection_support (left right : Hash) (domain : Slice U8)
    (same : SameFrames left right domain) (state : State) (count : Usize) (values : QValues) :
    prover_commit_reference.collect_qm31_owned left domain state count values =
      prover_commit_reference.collect_qm31_owned right domain state count values := by
  rw [ProverCommitMaterialRecursion.qm_extracted_finite left domain count.val count values state rfl,
    ProverCommitMaterialRecursion.qm_extracted_finite right domain count.val count values state rfl]
  exact qm_collection_support left right domain same _ values state

/-- All four families in the returned object use one retained material oracle.
Agreement on that domain transports the complete assembly, including errors,
balancing and final cursor; it requires no enumeration of 1024-row vectors. -/
theorem assembly_oracle_support (left right : Hash) (domain : Slice U8)
    (same : SameFrames left right domain) (state : State) (cells : Usize)
    (c1 : Values) (columns : alloc.vec.Vec Values) (g padding : QValues)
    (dependent : Usize) (active : Array Bool 1024#usize) (nonce : Array U8 32#usize) :
    assemble left domain state cells c1 columns g padding dependent active nonce =
    assemble right domain state cells c1 columns g padding dependent active nonce := by
  simp only [assemble,
    raw_collection_support left right domain same,
    indexed_columns_support left right domain same,
    qm_raw_collection_support left right domain same,
    indexed_padding_support left right domain same _ _ 0#usize _ _ (by decide)]

#print axioms field_roundtrip
#print axioms vector_roundtrip
#print axioms qm_raw_collection_support
#print axioms assembly_oracle_support
end R1Z.ProverCommitReturned16
