import Port4C_PrefixMeaning
import Port4C_InverseLoop
import Port4C_OwnedGeometryInverse

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryInverse
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}

def leaves (ops : Ops CoreError) : Port4C_NativePrefix.Leaves := ⟨ops.op9,ops.op7⟩
def prefixCall (ops : Ops CoreError) (flat : Slice U32) :=
  Port4C_NativePrefix.verifier.batch_prefix_products (leaves ops) flat

def install (ops : Ops CoreError) : Ops CoreError :=
  Port4C_GeometryStd.install {ops with op13 := prefixCall ops}

def vec (flat : Slice U32) : alloc.vec.Vec U32 := ⟨flat.val,flat.property⟩

theorem prefix_reference (ops : Ops CoreError)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.op7=ok (1#u32)) (flat : Slice U32) (bound : flat.val.length≤110) :
    prefixCall ops flat = (do
      let r ← S7Kani2PrefixLoop.prefixes_owned (vec flat) (alloc.vec.Vec.new U32) 1#u32 0#usize
      ok (r.2.1,r.2.2)) := by
  obtain ⟨cur,prod,run,meaning⟩ := Port4C_PrefixMeaning.total (leaves ops) multiply one flat bound
  obtain ⟨old,oldProd,oldRun,oldMeaning⟩ := S7Kani2PrefixLoop.prefixes_refines
    (vec flat) (alloc.vec.Vec.new U32) 1#u32 0#usize flat.val.length bound (by simp [vec]) (by simpa [vec] using bound)
  have sameModel : (cur.val,prod)=(old.val,oldProd) := by
    simpa only [vec,show (0#usize).val=0 from rfl,List.drop_zero,alloc.vec.Vec.new] using meaning.trans oldMeaning.symm
  have same : (cur,prod)=(old,oldProd) :=
    Prod.ext (Subtype.ext (congrArg (fun p : List U32 × U32 => p.1) sameModel)) (congrArg (fun p : List U32 × U32 => p.2) sameModel)
  change Port4C_NativePrefix.verifier.batch_prefix_products (leaves ops) flat = _
  rw [run,oldRun,bind_tc_ok]
  exact congrArg Result.ok same

def pipeline (ops : Ops CoreError) (flat inverse : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) := do
  let (prefixes,product) ← prefixCall ops flat.deref
  let suffix ← ops.op11 product
  Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 ops
    (Port4C_Reverse.reverse (alloc.vec.Vec.len flat)) flat prefixes suffix inverse

/-- CURRENT prefixCall plus CURRENT backward Vec loop implement the exact field
reciprocals. No prefixCall/inverse/backward-call success or output law is assumed. -/
theorem total (ops : Ops CoreError)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.op7=ok (1#u32))
    (inverseLeaf : ops.op11=Port4C_InverseExecution.inverse_owned)
    (flat inverse : alloc.vec.Vec U32) (bound : flat.val.length≤110)
    (size : inverse.val.length=flat.val.length)
    (nonzero : ∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) :
    ∃ out, pipeline ops flat inverse=ok out ∧ out.val.length=flat.val.length ∧
      ∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell out.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹ := by
  obtain ⟨out,run,hlen,hvalues⟩ := Port4C_OwnedGeometryInverse.total_exact flat
    (alloc.vec.Vec.new U32) inverse bound rfl size nonzero
  unfold Port4C_OwnedGeometryInverse.invert_owned at run
  obtain ⟨r,hprefix,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨suffix,hsuffix,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have native := Port4C_InverseLoop.from_owned ops multiply flat r.2.1 inverse out suffix
    (alloc.vec.Vec.len flat) bound run
  refine ⟨out,?_,hlen,hvalues⟩
  unfold pipeline
  rw [prefix_reference ops multiply one flat.deref bound]
  simp only [bind_assoc_eq,bind_tc_ok]
  change (do let r ← S7Kani2PrefixLoop.prefixes_owned flat (alloc.vec.Vec.new U32) 1#u32 0#usize
             let suffix ← ops.op11 r.2.2
             Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 ops
               (Port4C_Reverse.reverse (alloc.vec.Vec.len flat)) flat r.2.1 suffix inverse)=ok out
  rw [hprefix,bind_tc_ok,inverseLeaf,hsuffix,bind_tc_ok]
  exact native

#print axioms prefix_reference
#print axioms total
end AspisR1.Port4C_GeometryInverse
end
