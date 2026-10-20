import WireTx2Records
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.WireTx2
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Actual emitted occupied-parent body; both child widths come from Array. -/
theorem occupied_typed {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (values : Array Bytes32 16#usize) (index : Usize) (out : Bytes32)
    (h : multiproof.occupied_binary_parent D hash values index = ok out) :
    ∃ (left right : Bytes32),
      D.digest hash (nodeParts (Array.to_slice left) (Array.to_slice right)) = ok out ∧
      TypedInput (nodeParts (Array.to_slice left) (Array.to_slice right)) := by
  unfold multiproof.occupied_binary_parent at h
  simp only [lift, bind_tc_ok] at h
  obtain ⟨left, _, h⟩ := bind_success _ _ _ h
  obtain ⟨next, _, h⟩ := bind_success _ _ _ h
  obtain ⟨right, _, h⟩ := bind_success _ _ _ h
  exact ⟨left, right, h, .node _ _ left.property right.property⟩

/-- The helper accepts an arbitrary sibling slice. The width is supplied by
its calling loop's exact nodes[at..at+32] read, not by this API. -/
theorem sibling_typed {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (values : Array Bytes32 16#usize) (index : Usize) (sibling : Slice U8)
    (side : Bool) (out : Bytes32) (width : sibling.val.length = 32)
    (h : multiproof.sibling_binary_parent D hash values index sibling side = ok out) :
    ∃ (left right : Slice U8),
      D.digest hash (nodeParts left right) = ok out ∧ TypedInput (nodeParts left right) := by
  unfold multiproof.sibling_binary_parent at h
  cases side <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true,
    lift, bind_tc_ok] at h
  · obtain ⟨a, _, h⟩ := bind_success _ _ _ h
    exact ⟨sibling, Array.to_slice a, h, .node _ _ width a.property⟩
  · obtain ⟨a, _, h⟩ := bind_success _ _ _ h
    exact ⟨Array.to_slice a, sibling, h, .node _ _ a.property width⟩

/-- Missing width is a real obstruction: the helper's grammar has arbitrary
sibling length. This symbolic family cannot all be binary-node records. -/
theorem sibling_input_length (a : Bytes32) (s : Slice U8) :
    (inputBytes (nodeParts (Array.to_slice a) s)).length = 33 + s.val.length := by
  have ha : a.val.length = 32 := a.property
  change ([multiproof.BINARY_NODE_TAG] ++ (a.val ++ (s.val ++ []))).length = _
  simp only [List.length_append, List.length_cons, List.length_nil, ha]
  omega
#print axioms bind_success
#print axioms occupied_typed
#print axioms sibling_typed
#print axioms sibling_input_length
end AspisR1Stage2.WireTx2
