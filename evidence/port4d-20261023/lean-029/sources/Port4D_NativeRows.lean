import Port4D_Value
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_NativeRows
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev K := aspis_core.field.QM31
abbrev ExactK := OraclePortCheckpointAbiC5.K

theorem decode_field (q : K) : CheckpointBytes5Output.ofK q = Port4D_FlushRows.field q := by
  rfl

/-- Complete current value/map/finish parent is total on the reached length
class. TrustedStd content and retained S5 reducer interpretations are explicit
in map4/std; native pointer/ABI and current reducer binding remain ports. -/
theorem total (b : verifier.BatchedWeights) (old : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length) :
    ∃ out : Slice K, Port4D_Value.flush b old = ok out ∧
      out.val.length = old.val.length ∧
      (∀ q ∈ out.val, Port3_FlushInstall.Canonical q) ∧
      out.val.map CheckpointBytes5Output.ofK =
        (b.raw.val.take old.val.length).map S8JoinFinishField.rawValue := by
  obtain ⟨out,reference⟩ : ∃ out, Port3_FlushInstall.flush b old = ok out :=
    ⟨_,Port3_FlushInstall.flush_exact b old lengths⟩
  have run : Port4D_Value.flush b old = ok out := (Port4D_Value.reference_eq b old lengths).trans reference
  have h : Port4D_FlushRows.flush b old = ok out := (Port4D_Value.flush_eq b old).symm.trans run
  have rows := Port4D_FlushRows.accepted_rows b old out lengths h
  exact ⟨out,run,rows.2.1,rows.2.2,by
    simpa only [decode_field] using Port4D_FlushRows.accepted_field b old out lengths h⟩

/-- The observed raw64 field relation supplies the SAME source numeric decoder
used by checkpoint and finish. No second mathematical accumulator is chosen. -/
theorem materialized_weights (b : verifier.BatchedWeights) (loopOut : verifier.Accumulator)
    (w : Fin 64 → ExactK) (size : loopOut.weights.val.length = 64)
    (lengths : loopOut.weights.val.length ≤ b.raw.val.length)
    (meaning : ∀ (l : Fin 64) row, b.raw.val[l.val]? = some row → S8JoinFinishField.rawValue row = w l) :
    ∃ out : Slice K, Port4D_Value.flush b loopOut.weights.deref = ok out ∧
      (CheckpointBytes5Output.accumulator (Port4D_FlushRows.materialize loopOut out)).weights = w ∧
      (Port4D_FlushRows.materialize loopOut out).rhs = loopOut.rhs ∧
      (Port4D_FlushRows.materialize loopOut out).power = loopOut.power ∧
      (Port4D_FlushRows.materialize loopOut out).next = loopOut.next := by
  obtain ⟨out,run,len,canonical,fields⟩ := total b loopOut.weights.deref lengths
  have lists : out.val.map CheckpointBytes5Output.ofK = List.ofFn w := by
    rw [fields]
    apply List.ext_getElem
    · simp only [List.length_map,List.length_take,List.length_ofFn]
      change min loopOut.weights.val.length b.raw.val.length = 64
      rw [Nat.min_eq_left lengths,size]
    · intro j hj hk
      have bound : j<64 := by simpa only [List.length_ofFn] using hk
      have read : j<b.raw.val.length := by omega
      simp only [List.getElem_map,List.getElem_take,List.getElem_ofFn]
      exact meaning ⟨j,bound⟩ _ (List.getElem?_eq_getElem read)
  refine ⟨out,run,?_,rfl,rfl,rfl⟩
  funext l
  have bound : l.val<out.val.length := by change out.val.length = loopOut.weights.val.length at len; rw [len,size]; exact l.isLt
  have cell := congrArg (fun xs => xs[l.val]?) lists
  simp only [List.getElem?_map,List.getElem?_ofFn,dif_pos l.isLt,
    List.getElem?_eq_getElem bound,Option.map_some] at cell
  exact Option.some.inj cell

#print axioms decode_field
#print axioms total
#print axioms materialized_weights
end AspisR1.Port4D_NativeRows
end
