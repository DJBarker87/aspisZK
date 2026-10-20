import WireTx2ResumeCalls
import WireTx2LeafCalls
import WireTx2BinaryCalls
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.WireTx2

/-- Complete emitted resume success, caller sizes and concrete slice semantics
compose to three actual dictionary calls whose inputs are typed records. -/
theorem resume_typed (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (hp : proof.val.length = 57607) (ha : public1.val.length = 1880)
    (hc : bytes.val.length = 1768)
    (success : verifier.resumeWithOps ops D bytes proof public1 v hash = ok (.Ok (p,acc))) :
    ∃ (body : Slice U8) (d0 d1 d2 : Bytes32),
      D.digest hash (singletonParts proof) = ok d0 ∧
      D.digest hash (singletonParts public1) = ok d1 ∧
      D.digest hash (checksumParts body) = ok d2 ∧
      TypedInput (singletonParts proof) ∧ TypedInput (singletonParts public1) ∧
      TypedInput (checksumParts body) := by
  obtain ⟨finish, body, d0, d1, d2, hs, hr, h0, h1, h2⟩ :=
    resume_three_inputs ops D bytes proof public1 v hash p acc success
  have hb := checksum_body_width bytes body finish hc hs hr
  exact ⟨body, d0, d1, d2, h0, h1, h2,
    resume_binding_inputs_typed proof public1 body hp ha hb⟩

/-- Both actual sibling call branches are typed using their preceding emitted
checked-add/get operations; no independent sibling-width premise remains. -/
theorem sibling_read_typed {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (values : Array Bytes32 16#usize) (index : Usize)
    (nodes sibling : Slice U8) (at1 finish : Usize) (side : Bool) (out : Bytes32)
    (add : at1 + 32#usize = ok finish)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      nodes {start := at1, «end» := finish} = ok (some sibling))
    (call : multiproof.sibling_binary_parent D hash values index sibling side = ok out) :
    ∃ parts, D.digest hash parts = ok out ∧ TypedInput parts := by
  have hw := sibling_get_width nodes sibling at1 finish add get
  obtain ⟨left, right, hd, ht⟩ := sibling_typed D hash values index sibling side out hw call
  exact ⟨nodeParts left right, hd, ht⟩

/-- A trace composition lemma; caller must supply membership in the typed
site traces. It deliberately does not assert tx2's global trace correspondence. -/
theorem append_typed (a b : List (Slice (Slice U8)))
    (ha : ∀ x ∈ a, TypedInput x) (hb : ∀ x ∈ b, TypedInput x) :
    ∀ x ∈ a ++ b, TypedInput x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact hb x hx
/-- Counterexample input at the unrestricted public-rehash API: the empty
singleton has no D79 typed class. This is not a deployed-route counterexample. -/
theorem empty_public_not_typed (s : Slice U8) (empty : s.val.length = 0) :
    ¬ TypedInput (singletonParts s) := by
  intro ht
  obtain ⟨c, hc⟩ := typed_class_length _ ht
  rw [singleton_length, empty] at hc
  cases c <;> simp [AspisR1.WireBindingRecordCodec.Tx1Class.size] at hc
  rename_i kind
  cases kind <;> simp [AspisR1.WireBindingRecordCodec.BindingClass.size,
    AspisR1.WireBindingRecordCodec.proof_bytes_eq,
    AspisR1.WireBindingRecordCodec.asf8_size_eq] at hc
#print axioms empty_public_not_typed
#print axioms resume_typed
#print axioms sibling_read_typed
#print axioms append_typed
end AspisR1Stage2.WireTx2
