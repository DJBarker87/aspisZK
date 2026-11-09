import Port5Q2_ReaderScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderWeights
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev K := aspis_core.field.QM31
abbrev Iter := core.slice.iter.IterMut K

def intoIter (weights : alloc.vec.Vec K) : Result (Iter × (Iter → alloc.vec.Vec K)) :=
  ok (⟨weights.deref,0⟩,fun it => ⟨it.slice.val,it.slice.property⟩)
def weights_loop.body (read : CheckpointBytes4Sections.ReadK)
  (bytes : Slice Std.U8) (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (at1 : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.IterMut aspis_core.field.QM31) ×
    (core.slice.iter.IterMut aspis_core.field.QM31 → core.slice.iter.IterMut
    aspis_core.field.QM31) × Std.Usize) (Std.Usize × (Option
    (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    verifier.Error)) × (core.slice.iter.IterMut aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => let im := next_back iter1 none
            ok (done (at1, none, back im))
  | some _ =>
    let (r, reader) ← read { bytes, «at» := at1 }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (cont (iter1, fun im => let im1 := next_back im (some val)
                                 back im1, reader.«at»))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
          (core.convert.FromSame verifier.Error) residual
      let im := next_back iter1 o
      ok (done (at1, some r1, back im))

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop]
def weights_loop (read : CheckpointBytes4Sections.ReadK)
  (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (bytes : Slice Std.U8)
  (at1 : Std.Usize) :
  Result (Std.Usize × (Option (core.result.Result ((alloc.vec.Vec
    aspis_core.field.QM31) × Std.Usize) verifier.Error)) ×
    (core.slice.iter.IterMut aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1, at2) => weights_loop.body read
      bytes iter1 back1 at2)
    (iter, back, at1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 363:0-371:1 -/
def weights (read : CheckpointBytes4Sections.ReadK)
  (bytes : Slice Std.U8) (at1 : Std.Usize)
  (weights : alloc.vec.Vec aspis_core.field.QM31) :
  Result (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) ×
    Std.Usize) verifier.Error)
  := do
  let (iter, into_iter_back) ←
    intoIter weights
  let (at2, pending_return, back) ←
    weights_loop read iter (fun im => im) bytes at1
  match pending_return with
  | none =>
    let weights1 := into_iter_back back
    ok (core.result.Result.Ok (weights1, at2))
  | some r => ok r


/-- Fixed backing bytes are explicit in the CURRENT helper's recursion. -/
def reads (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8) :
    Nat → Usize → Result (core.result.Result (List K × Usize) verifier.Error)
  | 0, at1 => ok (.Ok ([],at1))
  | n+1, at1 => do
    let (value,out) ← read ⟨bytes,at1⟩
    match value with
    | .Err e => ok (.Err e)
    | .Ok x => do
      let tail ← reads read bytes n out.at
      match tail with
      | .Err e => ok (.Err e)
      | .Ok (xs,last) => ok (.Ok (x::xs,last))

def write (s : Slice K) (start : Nat) : List K → Slice K
  | [] => s
  | x::xs => (write s (start+1) xs).setAtNat start x

def finish (r : Usize × Option (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) × Iter) :
    Result (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) :=
  match r.2.1 with
  | none => ok (.Ok (⟨r.2.2.slice.val,r.2.2.slice.property⟩,r.1))
  | some v => ok v

/-- Deferred native iterator backwrites compose in source order; every read
outcome and short circuit is retained. This is a symbolic length induction. -/
theorem loop_exact (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8)
    (n : Nat) (it : Iter) (back : Iter → Iter) (at1 : Usize)
    (remaining : it.i+n=it.slice.val.length) :
    (do let r ← weights_loop read it back bytes at1; finish r) =
      (do let r ← reads read bytes n at1
          match r with
          | .Err e => ok (.Err e)
          | .Ok (xs,last) =>
            let final := back ⟨write it.slice it.i xs,it.i+n⟩
            ok (.Ok (⟨final.slice.val,final.slice.property⟩,last))) := by
  induction n generalizing it back at1 with
  | zero =>
    have inactive : ¬it.i<it.slice.len := by change ¬it.i<it.slice.val.length; omega
    unfold weights_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [weights_loop.body,core.slice.iter.IteratorIterMut.next,dif_neg inactive,
      bind_tc_ok,Aeneas.Std.uncurry,reads,finish,write,Nat.add_zero]
  | succ n ih =>
    have active : it.i<it.slice.len := by change it.i<it.slice.val.length; omega
    unfold weights_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [weights_loop.body,core.slice.iter.IteratorIterMut.next,dif_pos active,
      bind_tc_ok,Aeneas.Std.uncurry,reads,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair called
    rcases pair with ⟨value,out⟩
    cases value with
    | Err e => rfl
    | Ok x =>
      dsimp only
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
      rw [ih _ _ out.at (by change it.i+1+n=it.slice.val.length; omega)]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro rest decoded
      cases rest with
      | Err e => rfl
      | Ok pair =>
        rcases pair with ⟨xs,last⟩
        simp only [bind_tc_ok,write]
        have count : it.i+1+n=it.i+(n+1) := by omega
        rw [count]

#print axioms loop_exact
end AspisR1.Port5Q2_ReaderWeights
end
