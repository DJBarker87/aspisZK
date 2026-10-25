import T2Nat_QueryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderBody
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Try

/-- Source-order tail, factoring only the Try sequencing and 22 raw reads.
All source rejection branches and all actual record fields are retained. -/
def tail (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let different ← ops.ne core.cmp.PartialEqU8 checksum digest
  if different then ok (.Err .Checkpoint) else
    let (state,r1) ← ops.raw 32#usize ⟨bytes,80#usize⟩
    let (root0,r2) ← ops.raw 32#usize r1
    let (root1,r3) ← ops.raw 32#usize r2
    withRead (ops.readE r3) fun gamma r4 =>
    withRead (ops.readE r4) fun kappa r5 =>
    withRead (ops.readE r5) fun alpha0 r6 =>
    withRead (ops.readE r6) fun alpha1 r7 =>
    withRead (ops.readK r7) fun rho r8 => do
    let (queries,r9) ← T2Nat_QueryReads.queries ops.raw r8
    withOk (ops.validate queries) fun _ =>
    withOk (ops.readSemanticAlpha bytes r9.at) fun (semantic_alpha,at1) =>
    withRead (ops.readK {r9 with «at» := at1}) fun zx0 r10 =>
    withRead (ops.readK r10) fun zy0 r11 =>
    withRead (ops.readK r11) fun zx1 r12 =>
    withRead (ops.readK r12) fun zy1 r13 =>
    withRead (ops.readE r13) fun claim r14 =>
    withRead (ops.readE r14) fun rhs r15 =>
    withRead (ops.readK r15) fun power r16 => do
    let width ← ops.finalLen v
    let zero ← ops.zeroK
    withOk (ops.filled width zero) fun initial =>
    withOk (ops.readWeights bytes r16.at initial) fun (weights,at2) => do
    if at2 != finish then ok (.Err .Checkpoint) else
      let cursor ← lift (UScalar.cast .Usize next)
      ok (.Ok (⟨v,Array.make 2#usize [root0,root1],gamma,kappa,
        Array.make 2#usize [alpha0,alpha1],rho,queries,semantic_alpha,
        Array.make 2#usize [⟨zx0,zy0⟩,⟨zx1,zy1⟩],claim,state⟩,
        ⟨weights,rhs,power,cursor⟩))

theorem source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    tail ops bytes v next finish checksum digest =
      Port4A_NativeReader.tail ops bytes v next finish checksum digest := by
  simp only [tail,T2Nat_QueryReads.queries,withRead,withOk,
    Port4A_NativeReader.tail,T2Nat_Try.branch,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms source
end AspisR1.T2Nat_ReaderBody
end
