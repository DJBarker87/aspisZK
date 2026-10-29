import NEA_TableCanonical
import NEA_PointBridge
set_option autoImplicit false
namespace NEA_PointComplete
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual
open AspisR1.LPi_FieldValues NEA_FieldProduct

/-- Lower native CM31 bridge interpretation only. No geometry result or
successful enclosing call is a field. NBG/LPi supply this canonical law. -/
structure PhysicalInterpretation (cm : CM31Ops) : Prop where
  constructor : ∀ a b, cm.new a b=ok ⟨a,b⟩
  multiply : ∀ x y, Canonical x → Canonical y →
    ∃ z, cm.mul x y=ok z ∧ Canonical z ∧
      (z.a.val,z.b.val)=mulC (x.a.val,x.b.val) (y.a.val,y.b.val)

theorem emitted_interpretation : PhysicalInterpretation NEA_FieldProduct.ops :=
  ⟨fun _ _ => rfl,NEA_FieldProduct.geometric_cm⟩

theorem cohort (cm : CM31Ops) (physical : PhysicalInterpretation cm)
    (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (a b : U32 × U32) (z : field.CM31),
      Canonical z ∧
      (z.a.val,z.b.val)=mulC (a.1.val,a.2.val) (b.1.val,b.2.val) ∧
      NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (NEA_PointBridge.record a b z) ∧
      fast_domain.fibre_point cm u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨ix,iA,iB,a,b,get,same,mask,lo,shift,hi,readA,readB⟩ :=
    R17FibrePointActualSuccess.source_indices_and_table_reads u admitted
  have eq : ix=u := (Result.ok.inj get).symm
  subst ix
  have low : iA.val < 512 := by rw [lo]; exact Nat.mod_lt _ (by decide)
  have high : iB.val < 512 := by rw [hi]; unfold NEA_PointBridge.PacketDomain at admitted; omega
  have ca := NEA_TableCanonical.readA iA low a readA
  have cb := NEA_TableCanonical.readB iB high b readB
  obtain ⟨z,product,canonical,value⟩ := physical.multiply ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb
  have both := NEA_PointBridge.selected cm u iA iB a b z mask shift readA readB
    physical.constructor product
  exact ⟨a,b,z,canonical,value,both.1,both.2⟩

#print axioms emitted_interpretation
#print axioms cohort
end NEA_PointComplete
