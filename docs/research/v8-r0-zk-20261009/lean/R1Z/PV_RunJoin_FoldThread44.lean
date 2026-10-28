import R1Z.PV_RunJoin_DualCell44
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def step (q : Slice W) (alpha : W) (dual : Bool)
    (out : alloc.vec.Vec W) (i : Usize) : Result (alloc.vec.Vec W) := do
  let v0 ← Slice.index_usize q (Usize.wrapping_mul 4#usize i)
  let v1 ← Slice.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 1#usize)
  let v2 ← Slice.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 2#usize)
  let v3 ← Slice.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 3#usize)
  let z ← prover.fold_cell (Array.make 4#usize [v0,v1,v2,v3]) alpha dual
  alloc.vec.Vec.push out z

def phase (q : Slice W) (alpha : W) (dual : Bool) :
    Nat → alloc.vec.Vec W → Usize → Result (alloc.vec.Vec W)
  | 0,out,_ => .ok out
  | n+1,out,i => do
    let next ← step q alpha dual out i
    phase q alpha dual n next (Usize.wrapping_add i 1#usize)

theorem quotient (q : Slice W) :
    ∃ k : Usize, (Slice.len q / 4#usize : Result Usize) = .ok k ∧ k.val = q.length / 4 := by
  exact UScalar.div_spec (Slice.len q) (y := 4#usize) (by decide)

theorem stop (q : Slice W) (alpha : W) (dual : Bool) (out : alloc.vec.Vec W)
    (i : Usize) (bound : q.length / 4 ≤ i.val) :
    prover.fold_loop.body q alpha dual out i=.ok (.done out) := by
  obtain ⟨k,hk,hkv⟩ := quotient q
  unfold prover.fold_loop.body
  dsimp only
  rw [hk]
  simp only [bind_tc_ok,show ¬i < k from (by change ¬i.val < k.val;omega),↓reduceIte]

theorem one_step (q : Slice W) (alpha : W) (dual : Bool) (out : alloc.vec.Vec W)
    (i : Usize) (bound : i.val < q.length / 4) :
    prover.fold_loop.body q alpha dual out i=(do
      let next ← step q alpha dual out i
      .ok (.cont (next,Usize.wrapping_add i 1#usize))) := by
  obtain ⟨k,hk,hkv⟩ := quotient q
  unfold prover.fold_loop.body
  dsimp only
  rw [hk]
  simp only [bind_tc_ok,show i < k from (by change i.val < k.val;omega),
    ↓reduceIte,step,lift,bind_assoc_eq]

theorem complete (q : Slice W) (alpha : W) (dual : Bool) (n : Nat)
    (out : alloc.vec.Vec W) (i : Usize) (bound : i.val+n=q.length/4)
    (small : q.length/4≤256) :
    prover.fold_loop q alpha dual out i=phase q alpha dual n out i := by
  induction n generalizing out i with
  | zero =>
    unfold prover.fold_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop q alpha dual out i (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.fold_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step q alpha dual out i (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step q alpha dual out i))
    funext next
    apply ih next
    rw [PV_RunJoin_MergeLoop35.increment i (by omega)]
    omega

theorem caller (q : Slice W) (alpha : W) (dual : Bool) (small : q.length / 4 ≤ 256) :
    prover.fold q alpha dual = (do
      let count ← (Slice.len q / 4#usize : Result Usize)
      phase q alpha dual (q.length / 4) (alloc.vec.Vec.with_capacity W count) 0#usize) := by
  unfold prover.fold
  obtain ⟨k,hk,hkv⟩ := quotient q
  dsimp only
  rw [hk]
  simp only [bind_tc_ok]
  exact complete q alpha dual (q.length / 4) _ 0#usize (by change 0 + _ = _;omega) small
#print axioms quotient
#print axioms stop
#print axioms one_step
#print axioms complete
#print axioms caller
end R1Z.PV_RunJoin_FoldThread44
