import XRu_RowStep
import XRk_ResultTools
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowScalar
open XRu_RowShape XRk_ResultTools
theorem step0 (a b c d : U64) (l0 l1 l2 l3 basis : U32) (v : U64)
 (scalar : S7OwnedP6Scalar.residue_scalar_owned a l0 basis false=ok v) :
 verifier.update_residue_row_loop0.body (Array.make 4#usize [l0,l1,l2,l3])
  {start:=0#usize,«end»:=4#usize} (Array.make 4#usize [a,b,c,d]) basis =
 ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=1#usize,«end»:=4#usize},Array.make 4#usize [v,b,c,d],basis)) := by
 rw [XRu_RowStep.source _ _ _ 0#usize 1#usize (by decide) rfl]
 unfold S7OwnedP6Scalar.residue_scalar_owned at scalar
 simp only [lift,bind_tc_ok,Bool.false_eq_true,if_false] at scalar
 obtain ⟨product,hp,scalar⟩ := bind_success _ _ _ scalar
 obtain ⟨sum,hs,scalar⟩ := bind_success _ _ _ scalar
 cases Result.ok.inj scalar
 change (do
  let product ← (core.convert.num.FromU64U32.from l0) * (core.convert.num.FromU64U32.from basis)
  let sum ← a + product
  ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=1#usize,«end»:=4#usize},Array.make 4#usize [sum,b,c,d],basis))) = _
 rw [hp,bind_tc_ok,hs]
 rfl
#print axioms step0
theorem step1 (a b c d : U64) (l0 l1 l2 l3 basis : U32) (v : U64)
 (scalar : S7OwnedP6Scalar.residue_scalar_owned b l1 basis false=ok v) :
 verifier.update_residue_row_loop0.body (Array.make 4#usize [l0,l1,l2,l3])
  {start:=1#usize,«end»:=4#usize} (Array.make 4#usize [a,b,c,d]) basis =
 ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=2#usize,«end»:=4#usize},Array.make 4#usize [a,v,c,d],basis)) := by
 rw [XRu_RowStep.source _ _ _ 1#usize 2#usize (by decide) rfl]
 unfold S7OwnedP6Scalar.residue_scalar_owned at scalar
 simp only [lift,bind_tc_ok,Bool.false_eq_true,if_false] at scalar
 obtain ⟨product,hp,scalar⟩ := bind_success _ _ _ scalar
 obtain ⟨sum,hs,scalar⟩ := bind_success _ _ _ scalar
 cases Result.ok.inj scalar
 change (do
  let product ← (core.convert.num.FromU64U32.from l1) * (core.convert.num.FromU64U32.from basis)
  let sum ← b + product
  ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=2#usize,«end»:=4#usize},Array.make 4#usize [a,sum,c,d],basis))) = _
 rw [hp,bind_tc_ok,hs]
 rfl
#print axioms step1
theorem step2 (a b c d : U64) (l0 l1 l2 l3 basis : U32) (v : U64)
 (scalar : S7OwnedP6Scalar.residue_scalar_owned c l2 basis false=ok v) :
 verifier.update_residue_row_loop0.body (Array.make 4#usize [l0,l1,l2,l3])
  {start:=2#usize,«end»:=4#usize} (Array.make 4#usize [a,b,c,d]) basis =
 ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=3#usize,«end»:=4#usize},Array.make 4#usize [a,b,v,d],basis)) := by
 rw [XRu_RowStep.source _ _ _ 2#usize 3#usize (by decide) rfl]
 unfold S7OwnedP6Scalar.residue_scalar_owned at scalar
 simp only [lift,bind_tc_ok,Bool.false_eq_true,if_false] at scalar
 obtain ⟨product,hp,scalar⟩ := bind_success _ _ _ scalar
 obtain ⟨sum,hs,scalar⟩ := bind_success _ _ _ scalar
 cases Result.ok.inj scalar
 change (do
  let product ← (core.convert.num.FromU64U32.from l2) * (core.convert.num.FromU64U32.from basis)
  let sum ← c + product
  ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=3#usize,«end»:=4#usize},Array.make 4#usize [a,b,sum,d],basis))) = _
 rw [hp,bind_tc_ok,hs]
 rfl
#print axioms step2
theorem step3 (a b c d : U64) (l0 l1 l2 l3 basis : U32) (v : U64)
 (scalar : S7OwnedP6Scalar.residue_scalar_owned d l3 basis false=ok v) :
 verifier.update_residue_row_loop0.body (Array.make 4#usize [l0,l1,l2,l3])
  {start:=3#usize,«end»:=4#usize} (Array.make 4#usize [a,b,c,d]) basis =
 ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=4#usize,«end»:=4#usize},Array.make 4#usize [a,b,c,v],basis)) := by
 rw [XRu_RowStep.source _ _ _ 3#usize 4#usize (by decide) rfl]
 unfold S7OwnedP6Scalar.residue_scalar_owned at scalar
 simp only [lift,bind_tc_ok,Bool.false_eq_true,if_false] at scalar
 obtain ⟨product,hp,scalar⟩ := bind_success _ _ _ scalar
 obtain ⟨sum,hs,scalar⟩ := bind_success _ _ _ scalar
 cases Result.ok.inj scalar
 change (do
  let product ← (core.convert.num.FromU64U32.from l3) * (core.convert.num.FromU64U32.from basis)
  let sum ← d + product
  ok (@ControlFlow.cont (core.ops.range.Range Usize × Row × U32) Row ({start:=4#usize,«end»:=4#usize},Array.make 4#usize [a,b,c,sum],basis))) = _
 rw [hp,bind_tc_ok,hs]
 rfl
#print axioms step3
end XRu_RowScalar
