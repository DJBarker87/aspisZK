import NEA_PointParam.Funs
import NEA_FieldProduct
import R17FibrePointActualSuccess
set_option autoImplicit false
namespace NEA_PointBridge
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

def PacketDomain (u : Usize) : Prop := u.val < 262144

def record (a b : U32 × U32) (z : field.CM31) : Array U32 6#usize :=
  Array.make 6#usize [a.1,a.2,b.1,b.2,z.a,z.b]

/-- Reference-to-cohort association at the exact selected table inputs.
The product run is the named LOWER CM31 callee boundary, not a fibre-point
success premise. Canonical natural products are supplied by emitted_cm. -/
theorem selected (ops : CM31Ops) (u iA iB : Usize) (a b : U32 × U32)
    (z : field.CM31)
    (mask : lift (u &&& 511#usize)=ok iA)
    (shift : u >>> 9#i32=ok iB)
    (readA : Array.index_usize fast_domain.TABLE_A iA=ok a)
    (readB : Array.index_usize fast_domain.TABLE_B iB=ok b)
    (constructor : ∀ x y, ops.new x y=ok ⟨x,y⟩)
    (product : ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z) :
    NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (record a b z) ∧
    fast_domain.fibre_point ops u=ok ⟨z.a,z.b⟩ := by
  rcases a with ⟨a0,a1⟩
  rcases b with ⟨b0,b1⟩
  constructor
  · simp only [NEA_PointParam.point_ref,mask,shift,readA,readB,bind_tc_ok]
    simp [Array.index_usize,Array.make,record]
  · simp only [fast_domain.fibre_point,domain.FibreIndex.get,mask,shift,
      readA,readB,fast_domain.table_value,constructor,bind_tc_ok]
    dsimp only
    rw [product]
    rfl

/-- Every admitted index determines both reads, without assuming a successful
geometry computation. Native K010 supplies the canonical selected table data;
only the lower product interpretation is then required. -/
theorem reads (u : Usize) (admitted : PacketDomain u) :
    ∃ iA iB a b,
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b := by
  obtain ⟨ix,iA,iB,a,b,get,same,mask,_,shift,_,readA,readB⟩ :=
    R17FibrePointActualSuccess.source_indices_and_table_reads u admitted
  have eq : ix=u := by simpa [domain.FibreIndex.get] using (Result.ok.inj get).symm
  subst ix
  exact ⟨iA,iB,a,b,mask,shift,readA,readB⟩

#print axioms selected
#print axioms reads
end NEA_PointBridge
