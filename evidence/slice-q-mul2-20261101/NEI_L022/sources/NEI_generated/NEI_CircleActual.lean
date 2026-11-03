import NEI_CircleShared.Funs
import NEI_LineActual
import NEI_CircleDomains
set_option autoImplicit false
noncomputable section
namespace NEI_CircleActual
open Aeneas Aeneas.Std Result NEI_FieldCarriers NEI_FieldWide NEI_LineActual
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1

theorem body (alpha : N.E) (a : Array N.E 4#usize) (inverse : Array U32 5#usize) :
    resultMap toE (NEI_CircleShared.circle_fold_with_inverses alpha a inverse) =
      FIp_CircleSource.circle (toE alpha) (rows a) inverse := by
  obtain ⟨a,b,c,d,rfl⟩ := SAQ_LineArrays.four a
  obtain ⟨ix,iy,lx,ly,lz,rfl⟩ := SAQ_LineArrays.five inverse
  have mapped : rows (Array.make 4#usize [a,b,c,d]) =
      Array.make 4#usize [toE a,toE b,toE c,toE d] := rfl
  rw [mapped]
  have n0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = ok (a) := rfl
  have n1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = ok (b) := rfl
  have n2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = ok (c) := rfl
  have n3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = ok (d) := rfl
  have c0 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 0#usize = ok (toE a) := rfl
  have c1 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 1#usize = ok (toE b) := rfl
  have c2 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 2#usize = ok (toE c) := rfl
  have c3 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 3#usize = ok (toE d) := rfl
  have i0 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 0#usize = ok ix := rfl
  have i1 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 1#usize = ok iy := rfl
  simp only [NEI_CircleShared.circle_fold_with_inverses, FIp_CircleSource.circle,
    n0,n1,n2,n3,c0,c1,c2,c3,i0,i1,bind_tc_ok]
  simp only [bindE,bindWord,wide_add,wide_sub,wide_mul,wide_mul_m31,
    NEI_FieldScalar.m_mul,tofromE,NEI_CircleShared.QUARTER,SAQ_LineSource.quarter] <;> rfl

#print axioms body
end NEI_CircleActual
end
