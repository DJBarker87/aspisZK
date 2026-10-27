import XRm_ComplexValues
import XRm_TableBounds
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools XRm_FieldCanonical XRm_TableBlock
namespace XRm_PointInterpretation
abbrev F := XRm_FieldValues.M31Exact
theorem array_member {T : Type} {N : Usize} (a : Array T N) (i : Usize) (out : T)
    (run : Array.index_usize a i=ok out) : out ∈ a.val := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i value hread
    cases Result.ok.inj run
    exact List.mem_of_getElem? (by simpa only [Array.getElem?_Usize_eq] using hread)

theorem table_canonical (p : U32 × U32) (out : aspis_core.field.CM31) (good : Good p)
    (run : fast_domain.table_value p=ok out) : C out := by
  have same := Result.ok.inj run
  cases same
  exact good

/-- Mathematical interpretation of the two actual source-selected table
words and their complex product, in ZMod P. Both table bounds are proved from
the SAME emitted constants, through named 32-entry blocks. No table identity,
native allocator effect or source-to-ELF claim is folded into this theorem. -/
theorem point (u : aspis_core.r0.domain.FibreIndex)
    (out : aspis_core.r0.domain.Point aspis_core.field.M31)
    (run : fast_domain.fibre_point u=ok out) :
    ∃ high a b,
      u >>> 9#i32=ok high ∧
      Array.index_usize fast_domain.TABLE_A (u &&& 511#usize)=ok a ∧
      Array.index_usize fast_domain.TABLE_B high=ok b ∧
      (out.x.val:F)=(a.1.val:F)*(b.1.val:F)-(a.2.val:F)*(b.2.val:F) ∧
      (out.y.val:F)=(a.1.val:F)*(b.2.val:F)+(a.2.val:F)*(b.1.val:F) ∧
      M out.x ∧ M out.y := by
  obtain ⟨high,a,b,left,right,product,hh,ha,hb,hl,hr,hp,hx,hy,cx,cy⟩ := XRm_GeometryPoint.point u out run
  have ca := XRm_TableBounds.tableA a (array_member _ _ _ ha)
  have cb := XRm_TableBounds.tableB b (array_member _ _ _ hb)
  have values := XRm_ComplexValues.cmul left right product
    (table_canonical a left ca hl) (table_canonical b right cb hr) hp
  have left_eq := Result.ok.inj hl
  have right_eq := Result.ok.inj hr
  change (⟨a.1,a.2⟩ : aspis_core.field.CM31)=left at left_eq
  change (⟨b.1,b.2⟩ : aspis_core.field.CM31)=right at right_eq
  subst left
  subst right
  exact ⟨high,a,b,hh,ha,hb,by simpa only [hx] using values.1,
    by simpa only [hy] using values.2,cx,cy⟩
#print axioms array_member
#print axioms table_canonical
#print axioms point
end XRm_PointInterpretation
