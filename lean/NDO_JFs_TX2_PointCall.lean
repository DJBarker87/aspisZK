import JFs_TX2_GeometryLeaves
import RPt_JFs_TX2_ArrayRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_PointCall
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual

theorem source (u lo hi : Usize) (a b : U32 × U32)
    (mask : u &&& 511#usize=lo) (shift : u >>> 9#i32=ok hi)
    (ra : Array.index_usize fast_domain.TABLE_A lo=ok a)
    (rb : Array.index_usize fast_domain.TABLE_B hi=ok b)
    (ca : a.1.val<2147483647 ∧ a.2.val<2147483647)
    (cb : b.1.val<2147483647 ∧ b.2.val<2147483647) :
    ∃ point, fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point ∧
      point.x.val=ExtractedCurrentCM31Mul.realWord a.1.val a.2.val b.1.val b.2.val ∧
      point.y.val=ExtractedCurrentCM31Mul.imagWord a.1.val a.2.val b.1.val b.2.val ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 := by
  rcases a with ⟨a0,a1⟩
  rcases b with ⟨b0,b1⟩
  obtain ⟨z,hm,canon,vx,vy⟩ := ExtractedCurrentCM31Mul.current_mul_words
    (⟨a0,a1⟩ : AspisR1Qm31ArithmeticProbe.field.CM31)
    (⟨b0,b1⟩ : AspisR1Qm31ArithmeticProbe.field.CM31) ca cb
  have ta : fast_domain.table_value R17CurrentCM31Semantics.operations (a0,a1)=
      ok (⟨a0,a1⟩ : field.CM31) := rfl
  have tb : fast_domain.table_value R17CurrentCM31Semantics.operations (b0,b1)=
      ok (⟨b0,b1⟩ : field.CM31) := rfl
  have mm : R17CurrentCM31Semantics.operations.mul (⟨a0,a1⟩ : field.CM31) (⟨b0,b1⟩ : field.CM31)=
      ok (⟨z.a,z.b⟩ : field.CM31) := by
    change (do let r ← AspisR1Qm31ArithmeticProbe.field.CM31.mul
                 (⟨a0,a1⟩ : AspisR1Qm31ArithmeticProbe.field.CM31)
                 (⟨b0,b1⟩ : AspisR1Qm31ArithmeticProbe.field.CM31)
               ok (⟨r.a,r.b⟩ : field.CM31))=_
    rw [hm,bind_tc_ok]
  refine ⟨⟨z.a,z.b⟩,?_,vx,vy,canon.1,canon.2⟩
  simp only [fast_domain.fibre_point,domain.FibreIndex.get,lift,bind_tc_ok,mask,shift,ra,rb,ta,tb,mm]

#print axioms source
end AspisR1.JFs_TX2_PointCall
end
