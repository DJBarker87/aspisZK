import XRu_RowScalar
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowRun
open XRu_RowShape
/-- Symbolic composition of the four actual accepted scalar calls. -/
theorem source (a b c d x0 x1 x2 x3 : U64) (l0 l1 l2 l3 basis : U32)
 (h0 : S7OwnedP6Scalar.residue_scalar_owned a l0 basis false=ok x0)
 (h1 : S7OwnedP6Scalar.residue_scalar_owned b l1 basis false=ok x1)
 (h2 : S7OwnedP6Scalar.residue_scalar_owned c l2 basis false=ok x2)
 (h3 : S7OwnedP6Scalar.residue_scalar_owned d l3 basis false=ok x3) :
 verifier.update_residue_row_loop0 {start:=0#usize,«end»:=4#usize}
  (Array.make 4#usize [a,b,c,d]) basis (Array.make 4#usize [l0,l1,l2,l3]) =
 ok (Array.make 4#usize [x0,x1,x2,x3]) := by
 let limbs := Array.make 4#usize [l0,l1,l2,l3]
 let f := fun s : core.ops.range.Range Usize × Row × U32 =>
  verifier.update_residue_row_loop0.body limbs s.1 s.2.1 s.2.2
 change loop f ({start:=0#usize,«end»:=4#usize},Array.make 4#usize [a,b,c,d],basis)=_
 rw [loop.eq_def]
 rw [show f ({start:=0#usize,«end»:=4#usize},Array.make 4#usize [a,b,c,d],basis)=_
  from XRu_RowScalar.step0 a b c d l0 l1 l2 l3 basis x0 h0]
 simp only [bind_tc_ok]
 rw [loop.eq_def]
 rw [show f ({start:=1#usize,«end»:=4#usize},Array.make 4#usize [x0,b,c,d],basis)=_
  from XRu_RowScalar.step1 x0 b c d l0 l1 l2 l3 basis x1 h1]
 simp only [bind_tc_ok]
 rw [loop.eq_def]
 rw [show f ({start:=2#usize,«end»:=4#usize},Array.make 4#usize [x0,x1,c,d],basis)=_
  from XRu_RowScalar.step2 x0 x1 c d l0 l1 l2 l3 basis x2 h2]
 simp only [bind_tc_ok]
 rw [loop.eq_def]
 rw [show f ({start:=3#usize,«end»:=4#usize},Array.make 4#usize [x0,x1,x2,d],basis)=_
  from XRu_RowScalar.step3 x0 x1 x2 d l0 l1 l2 l3 basis x3 h3]
 simp only [bind_tc_ok]
 rw [loop.eq_def]
 have done : f ({start:=4#usize,«end»:=4#usize},Array.make 4#usize [x0,x1,x2,x3],basis)=
   ok (.done (Array.make 4#usize [x0,x1,x2,x3])) := by rfl
 rw [done]
#print axioms source
end XRu_RowRun
