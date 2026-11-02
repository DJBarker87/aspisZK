import R1Z.ProverRwFullFuns
import R1Z.ProverRw19LoopBind
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FieldValidation73
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def Cells (payload : Slice U8) (count : Usize) : Prop :=
  ∀ i : Usize, i.val<count.val → ∃ s w,
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      payload ({ start := Usize.wrapping_mul 32#usize i, «end» := Usize.wrapping_add (Usize.wrapping_mul 32#usize i) 32#usize } : core.ops.range.Range Usize)=ok s ∧
    aspis_core.field.wide_exact.WideExact.from_le_bytes s=ok (some w) ∧
    (do let h ← aspis_core.field.wide_exact.WideExact.impl.c1 w
        let z ← aspis_core.field.QM31.ZERO
        core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 h z)=ok false

theorem step (row : U8) (payload : Slice U8) (count i : Usize)
    (divide : Slice.len payload / 32#usize=ok count)
    (bound : i.val<count.val) (cells : Cells payload count) :
    host_wire.validate_record_fields_loop.body row payload i=
      ok (cont (Usize.wrapping_add i 1#usize)) := by
  obtain ⟨s,w,hs,hw,hzero⟩ := cells i bound
  have less : i<count := bound
  unfold host_wire.validate_record_fields_loop.body
  simp only [divide,bind_tc_ok,less,if_true,lift,hs,hw,core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch]
  change ((do
    let b ← (do
      let h ← aspis_core.field.wide_exact.WideExact.impl.c1 w
      let z ← aspis_core.field.QM31.ZERO
      core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 h z)
    if b then ok (done (core.result.Result.Err (r1_wire.Error.NonCanonical row i) : core.result.Result Unit r1_wire.Error))
    else ok (cont (Usize.wrapping_add i 1#usize))) = _)
  rw [hzero]
  rfl

theorem stop (row : U8) (payload : Slice U8) (count i : Usize)
    (divide : Slice.len payload / 32#usize=ok count) (bound : count.val ≤ i.val) :
    host_wire.validate_record_fields_loop.body row payload i=ok (done (.Ok ())) := by
  have less : ¬i<count := Nat.not_lt.mpr bound
  simp only [host_wire.validate_record_fields_loop.body,divide,bind_tc_ok,less,if_false]

theorem complete (row : U8) (payload : Slice U8) (count i : Usize) (n : Nat)
    (divide : Slice.len payload / 32#usize=ok count)
    (bound : i.val+n=count.val) (small : count.val<1024) (cells : Cells payload count) :
    host_wire.validate_record_fields_loop row payload i=ok (.Ok ()) := by
  induction n generalizing i with
  | zero =>
    unfold host_wire.validate_record_fields_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop row payload count i divide (by omega),bind_tc_ok]
  | succ n ih =>
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    unfold host_wire.validate_record_fields_loop
    rw [ProverRw19LoopBind.loop_bind]
    rw [step row payload count i divide (by omega) cells]
    simp only [bind_tc_ok]
    exact ih (Usize.wrapping_add i 1#usize) (by rw [inc];omega)

#print axioms Cells
#print axioms step
#print axioms stop
#print axioms complete
end R1Z.PV_RunJoin_FieldValidation73
