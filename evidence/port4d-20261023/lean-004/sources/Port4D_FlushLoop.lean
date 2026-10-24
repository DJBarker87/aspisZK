import Port4D_FlushStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FlushABI
open Aeneas Aeneas.Std Result ControlFlow
theorem finish_loop_output_invariant_of_step_laws
    (self : AspisR1Stage2.verifier.BatchedWeights)
    (value : AspisR1Stage2.verifier.BatchedWeights → Usize → Result K) (initial : FinishIter)
    (f : Nat → K)
    (hstart : initial.iter.i ≤ (initial.iter.slice.len).val)
    (hcount : initial.count.val = initial.iter.i)
    (hsome : some_step_law (value self) (initial.iter.slice.len).val f)
    (hnone : none_step_law (initial.iter.slice.len).val) :
    ∃ output : FinishBack,
      Port3_NativeFlushBody.verifier.BatchedWeights.finish_loop std value initial (fun e => e) self = .ok output ∧
      BackPrefix f initial.iter.i (initial.iter.slice.len).val output := by
  let total := (initial.iter.slice.len).val
  let body := fun s : FinishIter × FinishBack =>
    Port3_NativeFlushBody.verifier.BatchedWeights.finish_loop.body std value self s.1 s.2
  have hwp : WP.spec (loop body (initial, fun e => e))
      (BackPrefix f initial.iter.i total) := by
    refine loop.spec_decr_nat
      (fun s : FinishIter × FinishBack => total - s.1.iter.i)
      (fun s => initial.iter.i ≤ s.1.iter.i ∧ s.1.iter.i ≤ total ∧ s.1.iter.slice = initial.iter.slice ∧
        s.1.count.val = s.1.iter.i ∧
        BackPrefix f initial.iter.i s.1.iter.i s.2)
      (BackPrefix f initial.iter.i total)
      body (initial, fun e => e) ?_ ?_
    · rintro ⟨iter, back⟩ ⟨hlo, hi, hs, hc, hb⟩
      by_cases hlt : iter.iter.i < total
      · obtain ⟨index, x, iter1, nextBack, hnext, hindex, hi1, hs1, hc1, hvalue, hwrite⟩ :=
          hsome iter hlt hc (by simpa using congrArg (fun sl : FinishSlice => sl.len.val) hs)
        have hvalue' : value self index = .ok (f index.val) := hvalue
        have hbody : body (iter,back) = ok (.cont (iter1, fun e => back (nextBack e (some (index,f index.val))))) := by
          simp [body,Port3_NativeFlushBody.verifier.BatchedWeights.finish_loop.body,std,hnext,bind_tc_ok,hvalue']
        have hnextBack : BackPrefix f initial.iter.i (iter.iter.i + 1)
            (fun e => back (nextBack e (some (index, f index.val)))) :=
          backPrefix_step f initial.iter.i iter.iter.i back index nextBack hb hindex
            (by omega) (by intro e; simpa [hindex, hc] using hwrite e)
        have hinvNext : initial.iter.i ≤ iter1.iter.i ∧ iter1.iter.i ≤ total ∧
            iter1.iter.slice = initial.iter.slice ∧ iter1.count.val = iter1.iter.i ∧
            BackPrefix f initial.iter.i iter1.iter.i
              (fun e => back (nextBack e (some (index, f index.val)))) := by
          have hloNext : initial.iter.i ≤ iter1.iter.i := by rw [hi1]; exact Nat.le_succ_of_le hlo
          have hiNext : iter1.iter.i ≤ total := by rw [hi1]; exact Nat.succ_le_iff.mpr hlt
          have hcNext : iter1.count.val = iter1.iter.i := by rw [hi1]; exact hc1
          exact ⟨hloNext, hiNext, hs1.trans hs, hcNext,
            by simpa [hi1] using hnextBack⟩
        have hmeasure : total - iter1.iter.i < total - iter.iter.i := by omega
        simpa [body, hbody] using And.intro hinvNext hmeasure
      · obtain ⟨iter1, nextBack, hnext, hi1, hs1, hnoWrite⟩ :=
          hnone iter (by omega) (by simpa using congrArg (fun sl : FinishSlice => sl.len.val) hs)
        have hbody : body (iter,back) = ok (.done (fun e => back (nextBack e none))) := by
          simp [body,Port3_NativeFlushBody.verifier.BatchedWeights.finish_loop.body,std,hnext,bind_tc_ok]
        have hieq : iter.iter.i = total := Nat.le_antisymm hi (Nat.le_of_not_gt hlt)
        have hOutputSlice : BackPrefix f initial.iter.i total (fun e => back (nextBack e none)) := by
          intro e
          have hbp := hb (nextBack e none)
          rw [hnoWrite,hieq] at hbp
          exact hbp
        simpa [body, hbody] using hOutputSlice
    · exact ⟨le_rfl, hstart, rfl, hcount, backPrefix_id f initial.iter.i⟩
  obtain ⟨output, hrun, hout⟩ := WP.spec_imp_exists hwp
  refine ⟨output, ?_, hout⟩
  simpa [body, Port3_NativeFlushBody.verifier.BatchedWeights.finish_loop] using hrun


#print axioms finish_loop_output_invariant_of_step_laws
end AspisR1.Port4D_FlushABI
end
