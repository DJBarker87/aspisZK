import R1Z.PV_RDB1_PointerConstruct
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RDB1_V164

/-- The exact complete-Result call order of both owned index-loop bodies.
Arithmetic helpers are the SAME deployed monomorphizations, not assumed to
satisfy an old nightly body equation. Errors/divergence are not collapsed. -/
def body {M Q : Type} (scale : Q → M → Result Q) (add mul : Q → Q → Result Q)
    (values : Slice M) (lambda : Q) (state : Q × Q × Usize) :
    Result (ControlFlow (Q × Q × Usize) Q) := do
  let (out,power,i) := state
  if i < Slice.len values then
    let value ← Slice.index_usize values i
    let term ← scale power value
    let out' ← add out term
    let power' ← mul power lambda
    ok (cont (out',power',Usize.wrapping_add i 1#usize))
  else ok (done out)

def shipped {M Q : Type} (lift : M → Result Q) (scale : Q → M → Result Q)
    (add mul : Q → Q → Result Q) (tag : M) (values : Slice M) (lambda : Q) : Result Q := do
  let out ← lift tag
  loop (body scale add mul values lambda) (out,lambda,0#usize)

def reference {M Q : Type} (lift : M → Result Q) (scale : Q → M → Result Q)
    (add mul : Q → Q → Result Q) (tag : M) (values : Slice M) (lambda : Q) : Result Q := do
  let compressed ← lift tag
  loop (body scale add mul values lambda) (compressed,lambda,0#usize)

theorem complete {M Q : Type} (lift : M → Result Q) (scale : Q → M → Result Q)
    (add mul : Q → Q → Result Q) (tag : M) (values : Slice M) (lambda : Q) :
    shipped lift scale add mul tag values lambda =
      reference lift scale add mul tag values lambda := rfl

/-- At every executed iteration, the indexed read is within the initialized
slice and the machine increment cannot wrap. This uses the original Slice
representability bound and introduces no smaller input-length restriction. -/
theorem index_bounds {M : Type} (values : Slice M) (i : Usize)
    (h : i.val < values.val.length) :
    i.val < values.val.length ∧ i.val+1 ≤ values.val.length ∧
    i.val+1 < 2^UScalarTy.Usize.numBits := by
  have hv := (Slice.len values).hmax
  change values.val.length < 2^UScalarTy.Usize.numBits at hv
  omega

/-- Raw buffer read is the only memory access in the compressor control
loop; wrapping the same read continuation preserves any Result/effect carrier. -/
theorem pointer_read_complete {T P R : Type} (p : PV_RDB1_Pointer.Ptr T P)
    (read : PV_RDB1_Pointer.NonNull T P → Result R) :
    read (PV_RDB1_PointerConstruct.fromRef p) =
      read (PV_RDB1_PointerConstruct.transparentWrap p) := rfl

#print axioms complete
#print axioms index_bounds
#print axioms pointer_read_complete
end R1Z.PV_RDB1_V164
