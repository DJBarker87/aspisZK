import R1Z.ProverRwRngControl

/-! Concrete finite-provider instance of the actual emitted owner. Tape
exhaustion is extraction failure, never an invented OS error. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngTape
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngControl
variable [ErasureFns]
abbrev Reply := Array U8 64#usize × core.result.Result Unit U8

def tape (replies : List Reply) (bound : replies.length ≤ Usize.max) (used : Usize) : Tape :=
  ⟨⟨replies,bound⟩,used⟩

theorem fill_at (replies : List Reply) (bound : replies.length ≤ Usize.max)
    (index : Usize) (inside : index.val < replies.length) (input : Array U8 64#usize) :
    Tape.Insts.Prover_rw_rng_preflightDraw64.fill (tape replies bound index) input = (do
      let following ← index + 1#usize
      .ok ((tape replies bound following,(replies[index.val]).2),(replies[index.val]).1)) := by
  unfold Tape.Insts.Prover_rw_rng_preflightDraw64.fill tape
  have go : index < alloc.vec.Vec.len (⟨replies,bound⟩ : alloc.vec.Vec Reply) := by
    change index.val < replies.length
    exact inside
  simp only [go,massert,if_true,bind_tc_ok,alloc.vec.Vec.index_slice_index]
  have hi : index.val < alloc.vec.Vec.length (⟨replies,bound⟩ : alloc.vec.Vec Reply) := inside
  obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec
    (⟨replies,bound⟩ : alloc.vec.Vec Reply) index hi)
  rw [hx]
  simp only [bind_tc_ok,hv]
  generalize replies[index.val] = entry
  rcases entry with ⟨block,status⟩
  rfl

/-- Primitive replies mention actual successive provider states, not an owner
output equality. All retry/success conclusions follow from emitted control. -/
theorem zero_then_one_loop {P : Type} (draw : Draw64 P) (p0 p1 p2 : P)
    (nonce : Array U8 32#usize)
    (first : draw.fill p0 (Array.repeat 64#usize 0#u8) =
      .ok ((p1,.Ok ()),Array.repeat 64#usize 0#u8))
    (second : draw.fill p1 (Array.repeat 64#usize 0#u8) =
      .ok ((p2,.Ok ()),Array.repeat 64#usize 1#u8)) :
    StateOnlyAttemptSecrets.generate_with_loop draw nonce p0 16#usize 0#usize =
      .ok (p2,.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩) := by
  have zero := constant_step draw p0 p1 nonce 0#usize 16#usize (by decide)
    0#u8 (by rfl) (by rfl) first
  have one := constant_step draw p1 p2 nonce 1#usize 16#usize (by decide)
    1#u8 (by rfl) (by rfl) second
  have add : ((0#usize) + 1#usize : Result Usize) = .ok (1#usize) := by
    rw [ProverRwSamplerArithmetic.add_exact 0#usize 1#usize (by scalar_tac)]
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    change 1 % UScalar.size .Usize = 1
    exact Nat.mod_eq_of_lt (1#usize).hSize
  simp only [show (0#u8 != 0#u8) = false from rfl,Bool.false_eq_true,if_false,add,bind_tc_ok] at zero
  simp only [show (1#u8 != 0#u8) = true from rfl,if_true] at one
  let step : P × Usize → Result (ControlFlow (P × Usize) (P × Status)) :=
    fun state => body draw nonce 16#usize state.1 state.2
  change loop step (p0,0#usize) = _
  rw [loop]
  simp only [step,zero,bind_tc_ok]
  rw [loop]
  simp only [step,one,bind_tc_ok]

/-- Both successful draws come from one actual finite provider. The untouched
suffix remains in the returned state and the cursor is two, including the
rejected first reply. The nonce is admitted by the emitted guard itself. -/
theorem concrete_zero_then_one (rest : List Reply)
    (bound : rest.length + 2 ≤ Usize.max) :
    let replies : List Reply :=
      (Array.repeat 64#usize 0#u8,.Ok ()) ::
      (Array.repeat 64#usize 1#u8,.Ok ()) :: rest
    let fits : replies.length ≤ Usize.max := by
      simp only [replies,List.length_cons]
      omega
    owner (Array.repeat 32#usize 1#u8) (tape replies fits 0#usize) =
      .ok (tape replies fits 2#usize,.Ok
        ⟨Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩) := by
  dsimp only
  let replies : List Reply :=
    (Array.repeat 64#usize 0#u8,.Ok ()) ::
    (Array.repeat 64#usize 1#u8,.Ok ()) :: rest
  have fits : replies.length ≤ Usize.max := by
      simp only [replies,List.length_cons]
      omega
  have add01 : ((0#usize) + 1#usize : Result Usize) = .ok (1#usize) := by
    rw [ProverRwSamplerArithmetic.add_exact 0#usize 1#usize (by scalar_tac)]
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    change 1 % UScalar.size .Usize = 1
    exact Nat.mod_eq_of_lt (1#usize).hSize
  have add12 : ((1#usize) + 1#usize : Result Usize) = .ok (2#usize) := by
    rw [ProverRwSamplerArithmetic.add_exact 1#usize 1#usize (by scalar_tac)]
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    change 2 % UScalar.size .Usize = 2
    exact Nat.mod_eq_of_lt (2#usize).hSize
  have first := fill_at replies fits 0#usize (by simp [replies]) (Array.repeat 64#usize 0#u8)
  have second := fill_at replies fits 1#usize (by simp [replies]) (Array.repeat 64#usize 0#u8)
  simp only [add01,bind_tc_ok] at first
  simp only [add12,bind_tc_ok] at second
  unfold owner StateOnlyAttemptSecrets.generate_with
  rw [ProverRwRngNonzero.nonzero_repeat 1#u8 (by rfl) (by rfl)]
  simp only [bind_tc_ok]
  unfold ENTROPY_RETRY_LIMIT
  exact zero_then_one_loop Tape.Insts.Prover_rw_rng_preflightDraw64
    (tape replies fits 0#usize) (tape replies fits 1#usize) (tape replies fits 2#usize)
    (Array.repeat 32#usize 1#u8) first second

#print axioms concrete_zero_then_one

#print axioms fill_at
#print axioms zero_then_one_loop
end R1Z.ProverRwRngTape

-- Focused final audit of the exact imported predecessor statements.
#print ProverRwRng.Draw64
#print ProverRwRng.StateOnlyAttemptSecrets.generate_with
#print axioms R1Z.ProverRwRngNonzero.index_repeat
#print axioms R1Z.ProverRwRngNonzero.scan_fixed
#print axioms R1Z.ProverRwRngNonzero.nonzero_repeat
#print axioms R1Z.ProverRwRngControl.constant_step
#print axioms R1Z.ProverRwRngControl.error_state
#print axioms R1Z.ProverRwRngControl.cap_state
