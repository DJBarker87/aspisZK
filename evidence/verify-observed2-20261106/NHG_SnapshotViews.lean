import NHG_Semantic
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_SnapshotViews
abbrev Digest := Array U32 8#usize
abbrev Frontier := Array Digest 20#usize
abbrev Transition := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Views := U64 × Frontier × Digest × Frontier

def view (t : Transition) : Views :=
 (t.live_snapshot.next_pair_index,t.live_snapshot.frontier,
  t.candidate_afterstate.next_root,t.candidate_afterstate.next_frontier)

def oldView (t : AspisR1PublicSerializer.Whole431.Transition) : Views :=
 (t.live_snapshot.next_pair_index,t.live_snapshot.frontier,
  t.candidate_afterstate.next_root,t.candidate_afterstate.next_frontier)

def publicView (p : NHG_Serializer.Public) : Views := view (NHG_Semantic.value p).transition

theorem actual (p : NHG_Serializer.Public) :
 (do let semantic ← p.semantic;ok (view semantic.transition))=ok (publicView p) := by
 rw [NHG_Semantic.source]
 rfl

theorem carrier (p : NHG_Serializer.Public) :
 publicView p=match p with
 | .Transfer _ t => oldView (SerializerWhole.toTransition t)
 | .Withdrawal _ t => oldView (SerializerWhole.toTransition t) := by
 cases p <;> rfl

/-- One arbitrary observed coordinate identifies the complete array. This
lifts the native copy window without executing an entire copy in Kani. -/
theorem array_ext {A : Type} {n : Usize} (x y : Array A n)
 (same : ∀ i (hi : i<n.val),x.val[i]'(by simpa [x.property] using hi)=
 y.val[i]'(by simpa [y.property] using hi)) : x=y := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact x.property.trans y.property.symm
 · intro i hi hj
   exact same i (by simpa [x.property] using hi)

theorem frontier_ext (x y : Frontier)
 (same : ∀ (r : Fin 20) (k : Fin 8),
  (x.val[r.val]'(by simpa [x.property] using r.isLt)).val[k.val]'(by
    simpa [(x.val[r.val]'(by simpa [x.property] using r.isLt)).property] using k.isLt)=
  (y.val[r.val]'(by simpa [y.property] using r.isLt)).val[k.val]'(by
    simpa [(y.val[r.val]'(by simpa [y.property] using r.isLt)).property] using k.isLt)) : x=y := by
 apply array_ext x y
 intro r hr
 apply array_ext
 intro k hk
 exact same ⟨r,by simpa using hr⟩ ⟨k,by simpa using hk⟩

#print axioms actual
#print axioms carrier
#print axioms array_ext
#print axioms frontier_ext
end AspisR1.NHG_SnapshotViews
