import V7ProductionCallbacksR30MutableCanonical
import V7ProductionCallbacksR30PackedDecoderCanonical

/-! Canonicality of the literal C1 slot-major gamma output. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30GammaC1Canonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30KaratsubaCanonical
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26FieldBridge

abbrev LiteralQM31 := V7GammaSlotMajorLiteral.field.QM31
abbrev Powers := V7GammaSlotMajorLiteral.state_only_spend_query.StateOnlySpendQueryPowers
abbrev Iter := Enum LiteralQM31
abbrev State := Iter × (Iter → Iter) × Powers

local instance : Inhabited LiteralQM31 := ⟨V7GammaSlotMajorLiteral.field.QM31.ZERO⟩

def LiteralCanonical (value : LiteralQM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c0.a.val ∧
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c0.b.val ∧
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c1.a.val ∧
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c1.b.val

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem literal_reduce_canonical (value : Std.U64) (output : Std.U32)
    (run : V7GammaSlotMajorLiteral.field.M31.reduce_u64 value = ok output) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  have reduceEq : V7GammaSlotMajorLiteral.field.M31.reduce_u64 value =
      V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64 value := by
    unfold V7GammaSlotMajorLiteral.field.M31.reduce_u64
      V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64
      V7GammaSlotMajorLiteral.field.reduce_u64
      V7ProductionCallbacksR29.aspis_core.field.reduce_u64
    have pExact : V7GammaSlotMajorLiteral.field.P =
        V7ProductionCallbacksR29.aspis_core.field.P := by
      rw [V7ProductionCallbacksR30FieldCanonical.p_eq]
      simp only [V7GammaSlotMajorLiteral.field.P, V7CallerCurrentReleaseR26.field.P]
    rw [pExact]
  rw [reduceEq] at run
  exact successful_callback_reduce_canonical value output run

private def body (c1 : Array Std.U32 104#usize) (state : State) :
    Result (ControlFlow State (Iter → Iter)) :=
  V7GammaSlotMajorLiteral.v6_onefold.gamma_combine_v6_c1_slot_major_loop0.body
    c1 state.1 state.2.1 state.2.2

private theorem trace_back_canonical
    (c1 : Array Std.U32 104#usize) {state : State} {output : Iter → Iter}
    (trace : ExactLoopTrace (body c1) state output) :
    SliceAll LiteralCanonical state.1.iter.slice →
    BackAll LiteralCanonical state.2.1 → BackAll LiteralCanonical output := by
  induction trace with
  | @done state output edge =>
      intro initial backCanonical
      unfold body at edge
      unfold V7GammaSlotMajorLiteral.v6_onefold.gamma_combine_v6_c1_slot_major_loop0.body at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨⟨option, nextIter, nextBack⟩, nextRun, edge⟩ := edge
      cases option with
      | none =>
          have exactOutput := ControlFlow.done.inj (Result.ok.inj edge)
          rw [← exactOutput]
          intro candidate canonical
          apply backCanonical
          exact enumerate_none_back_all LiteralCanonical _ _ _ nextRun candidate canonical
      | some pair =>
          repeat' (rw [bind_eq_ok_iff] at edge; obtain ⟨_, _, edge⟩ := edge)
          cases edge
  | @cont state next output edge tail ih =>
      intro initial backCanonical
      unfold body at edge
      unfold V7GammaSlotMajorLiteral.v6_onefold.gamma_combine_v6_c1_slot_major_loop0.body at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨⟨option, nextIter, nextBack⟩, nextRun, edge⟩ := edge
      cases option with
      | none => cases edge
      | some pair =>
          rcases pair with ⟨slot, oldValue⟩
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨groupCount, groupCountRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨groupResult, groupResultRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨start, startRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨rawResult, rawResultRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨sums, sumsRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨wide0, wide0Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨m0, m0Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨wide1, wide1Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨m1, m1Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨cm0, cm0Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨wide2, wide2Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨m2, m2Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨wide3, wide3Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨m3, m3Run, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨cm1, cm1Run, edge⟩ := edge
          have cm0Exact : cm0 = ⟨m0, m1⟩ := (Result.ok.inj cm0Run).symm
          have cm1Exact : cm1 = ⟨m2, m3⟩ := (Result.ok.inj cm1Run).symm
          have valueCanonical : LiteralCanonical ⟨cm0, cm1⟩ := by
            rw [cm0Exact, cm1Exact]
            exact ⟨literal_reduce_canonical wide0 m0 m0Run,
              literal_reduce_canonical wide1 m1 m1Run,
              literal_reduce_canonical wide2 m2 m2Run,
              literal_reduce_canonical wide3 m3 m3Run⟩
          have stateExact := ControlFlow.cont.inj (Result.ok.inj edge)
          have facts := enumerate_some_all LiteralCanonical _ _ _ slot oldValue nextRun initial
          apply ih
          · rw [← stateExact]
            exact facts.2.1
          · rw [← stateExact]
            intro candidate canonical
            apply backCanonical
            exact facts.2.2 _ valueCanonical candidate canonical

theorem literal_c1_gamma_canonical
    (c1 : Array Std.U32 104#usize) (powers : Powers)
    (output : Array LiteralQM31 4#usize)
    (run : V7GammaSlotMajorLiteral.v6_onefold.gamma_combine_v6_c1_slot_major c1 powers =
      ok output) : SliceAll LiteralCanonical output.to_slice := by
  let initial := Array.repeat 4#usize V7GammaSlotMajorLiteral.field.QM31.ZERO
  let iter : Iter := ⟨⟨initial.to_slice, 0⟩, 0#usize⟩
  have initialCanonical : SliceAll LiteralCanonical initial.to_slice := by
    intro index bound
    have indexBound : index < 4 := by simpa [initial, Array.to_slice] using bound
    have valueExact : initial.to_slice.val[index]! = V7GammaSlotMajorLiteral.field.QM31.ZERO := by
      change (List.replicate 4 V7GammaSlotMajorLiteral.field.QM31.ZERO)[index]! = _
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_replicate_of_lt indexBound, Option.getD_some]
    rw [valueExact]
    simp [
      V7GammaSlotMajorLiteral.field.QM31.ZERO, LiteralCanonical,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus]
  unfold V7GammaSlotMajorLiteral.v6_onefold.gamma_combine_v6_c1_slot_major at run
  simp only [Array.to_slice_mut, core.slice.Slice.iter_mut,
    core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate, Std.lift, bind_tc_ok] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨back, loopRun, run⟩ := run
  have loopExact : loop (body c1) (iter, (fun e => e), powers) = ok back := loopRun
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (body c1) (iter, (fun e => e), powers) back loopExact
  have backCanonical := trace_back_canonical c1 trace initialCanonical (fun _ canonical => canonical)
  have sliceCanonical := backCanonical iter initialCanonical
  have outputExact := Result.ok.inj run
  rw [← outputExact]
  change SliceAll LiteralCanonical (Array.from_slice initial (back iter).iter.slice).to_slice
  unfold Array.from_slice
  split
  · exact sliceCanonical
  · exact initialCanonical

#print axioms literal_c1_gamma_canonical

local instance : Inhabited V7ProductionCallbacksR30Qm31Canonical.CallbackQM31 :=
  ⟨V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩

theorem callback_c1_gamma_canonical
    (c1 : Array Std.U32 104#usize)
    (powers : V7ProductionCallbacksR29.aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : Array V7ProductionCallbacksR30Qm31Canonical.CallbackQM31 4#usize)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_c1_slot_major
      c1 powers = ok output) : SliceAll GeneratedCanonicalQM31 output.to_slice := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.gamma_combine_v6_c1_slot_major at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨literal, literalRun, run⟩ := run
  have literalCanonical := literal_c1_gamma_canonical c1 _ literal literalRun
  have outputExact := Result.ok.inj run
  rw [← outputExact]
  intro index bound
  let mapped := V7ProductionCallbacksR29HelpersSplit.mapArray
    V7ProductionCallbacksR29HelpersSplit.fromGammaQM31 literal
  have indexBound : index < mapped.val.length := bound
  have member : mapped.val[index]! ∈ mapped.val := by
    rw [← List.Inhabited_getElem_eq_getElem! mapped.val index indexBound]
    exact List.getElem_mem indexBound
  change mapped.val[index]! ∈ literal.val.map V7ProductionCallbacksR29HelpersSplit.fromGammaQM31 at member
  obtain ⟨value, valueMember, mappedExact⟩ := List.mem_map.mp member
  obtain ⟨position, positionBound, valueExact⟩ := List.mem_iff_getElem.mp valueMember
  have valueCanonical := literalCanonical position positionBound
  change LiteralCanonical literal.val[position]! at valueCanonical
  rw [← List.Inhabited_getElem_eq_getElem! literal.val position positionBound,
    valueExact] at valueCanonical
  change GeneratedCanonicalQM31 mapped.val[index]!
  rw [← mappedExact]
  exact ⟨⟨valueCanonical.1, valueCanonical.2.1⟩,
    ⟨valueCanonical.2.2.1, valueCanonical.2.2.2⟩⟩

#print axioms callback_c1_gamma_canonical
end V7ProductionCallbacksR30GammaC1Canonical
