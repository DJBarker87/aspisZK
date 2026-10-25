import T2Nat_ReaderFission
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
    T2Nat_ReaderSuffix.normalized ops bytes v next finish state root0 root1
      gamma kappa alpha0 alpha1 rho queries semantic_alpha {r9 with «at» := at1}


theorem source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    tail ops bytes v next finish checksum digest =
      Port4A_NativeReader.tail ops bytes v next finish checksum digest := by
  rw [← T2Nat_ReaderFission.source]
  simp only [tail,T2Nat_QueryReads.queries,withRead,withOk,
    T2Nat_ReaderFission.tail,T2Nat_ReaderSuffix.normalize,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  repeat
    first
    | rfl
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro x hx; try rcases x with ⟨a,b⟩)
    | (simp only [bind_tc_ok,Aeneas.Std.uncurry])
    | (split <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,Aeneas.Std.uncurry])

#print axioms source
end AspisR1.T2Nat_ReaderBody
end
