import NEA_PointComplete
set_option autoImplicit false
namespace NEB_PointCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

/-- The callee's non-root physical interpretation is instantiated, not retained. -/
theorem canonical_point (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ p : domain.Point field.M31,
      fast_domain.fibre_point NEA_FieldProduct.ops u=ok p ∧
      p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  obtain ⟨a,b,z,canonical,_,_,point⟩ :=
    NEA_PointComplete.cohort NEA_FieldProduct.ops NEA_PointComplete.emitted_interpretation u admitted
  exact ⟨⟨z.a,z.b⟩,point,canonical.1,canonical.2⟩

/-- Exact selected operands establish the lower CM31 packet at this call. -/
theorem selected_product (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (iA iB : Usize) (a b : U32 × U32) (z : field.CM31),
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b ∧
      NEA_FieldProduct.Canonical ⟨a.1,a.2⟩ ∧
      NEA_FieldProduct.Canonical ⟨b.1,b.2⟩ ∧
      NEA_FieldProduct.ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      NEA_FieldProduct.Canonical z ∧
      fast_domain.fibre_point NEA_FieldProduct.ops u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨ix,iA,iB,a,b,get,same,mask,lo,shift,hi,readA,readB⟩ :=
    R17FibrePointActualSuccess.source_indices_and_table_reads u admitted
  have eq : ix=u := (Result.ok.inj get).symm
  subst ix
  have low : iA.val<512 := by rw [lo]; exact Nat.mod_lt _ (by decide)
  have high : iB.val<512 := by rw [hi]; unfold NEA_PointBridge.PacketDomain at admitted; omega
  have ca := NEA_TableCanonical.readA iA low a readA
  have cb := NEA_TableCanonical.readB iB high b readB
  obtain ⟨z,product,cz,_⟩ := NEA_PointComplete.emitted_interpretation.multiply
    ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb
  have selected := NEA_PointBridge.selected NEA_FieldProduct.ops u iA iB a b z
    mask shift readA readB NEA_PointComplete.emitted_interpretation.constructor product
  exact ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,product,cz,selected.2⟩

def pureState {A S Event : Type} (s : S) (r : Result A) : Result (A × S × List Event) := do
  let z ← r
  ok (z,s,[])

/-- The emitted field/table operations are pure; the native bridge separately
certifies its ghost-only frame. This lift is not a native evaluator. -/
theorem state_effects {S Event : Type} (s : S) (u : Usize)
    (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ p : domain.Point field.M31,
      pureState (Event:=Event) s (fast_domain.fibre_point NEA_FieldProduct.ops u)=ok (p,s,[]) ∧
      p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  obtain ⟨p,run,cx,cy⟩ := canonical_point u admitted
  exact ⟨p,by simp only [pureState,run,bind_tc_ok],cx,cy⟩

#print axioms canonical_point
#print axioms selected_product
#print axioms state_effects
end NEB_PointCalls
