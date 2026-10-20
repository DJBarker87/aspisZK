import S4FromFnP6OuterSameClosureLoop0V1
import S4FromFnP6Loop0ArrayOpIrrelevanceV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

private abbrev OutputStepBy := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
private def outputLinkStartBy : OutputStepBy :=
  { iter := { start := 0#usize, «end» := 26#usize }, step_by := 4#usize }
private theorem outputLinkStepBy :
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize = .ok outputLinkStartBy := by
  simp [outputLinkStartBy, core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default]

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem generatedCallback_success_output_link
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (c : fast_dots.four_dots.closure) (slot : Usize)
    {value : aspis_core.field.wide_exact.WideExact}
    {c' : fast_dots.four_dots.closure}
    (h : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops) c slot = .ok (value,c')) :
    ∃ (a : Aeneas.Std.Array Std.U8 608#usize)
      (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
      (iter : OutputStepBy)
      (limbs : Aeneas.Std.Array Std.U64 8#usize)
      (vals : Aeneas.Std.Array Std.U32 8#usize)
      (optValue : Option aspis_core.field.wide_exact.WideExact)
      (bodyValue : aspis_core.field.wide_exact.WideExact)
      (tailValue : aspis_core.field.wide_exact.WideExact),
      c = (a,g) ∧
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := 26#usize } 4#usize = .ok iter ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) iter a g slot
        (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok vals ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).wideFromLimbs vals = .ok optValue ∧
      core.option.Option.unwrap optValue = .ok bodyValue ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).wideAdd bodyValue tailValue = .ok value := by
  cases c with
  | mk a g =>
      change fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (packClosure a g) slot = .ok (value,c') at h
      rw [full_pack] at h
      rw [fullCore_factor] at h
      obtain ⟨pair, hprefix, hadd⟩ := bind_success _ _ _ h
      rcases pair with ⟨bodyValue, tailValue⟩
      obtain ⟨sumValue, haddop, hret⟩ := bind_success _ _ _ hadd
      have hret' := Result.ok.inj hret
      have hsum : sumValue = value := (Prod.mk.inj hret').1
      subst sumValue
      unfold prefixCore at hprefix
      obtain ⟨iter,hstep,hrest⟩ := bind_success _ _ _ hprefix
      obtain ⟨limbs,hloop,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨vals,harray,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨optValue,hwide,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨unwrapped,hunwrap,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨tail,hnew,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨we,hindex,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i,hmul,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i1,hadd104,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨i2,hadd120,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨s,hslice,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨optQ,hqm,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨q,hunq,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨pushed,hpush,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨unitValue,hunwrapPush,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨tail2,hloop1,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨tailValue',hfinish,hfinal⟩ := bind_success _ _ _ hrest
      have hunwrapValue : unwrapped = bodyValue := by
        have := Result.ok.inj hfinal
        exact (Prod.mk.inj this).1
      have htailValue : tailValue' = tailValue := by
        have := Result.ok.inj hfinal
        exact (Prod.mk.inj this).2
      subst tailValue'
      subst unwrapped
      exact ⟨a,g,iter,limbs,vals,optValue,bodyValue,tailValue,rfl,
        hstep,hloop,harray,hwide,hunwrap,haddop⟩

#print axioms generatedCallback_success_output_link
end AspisR1FromFnP6Generated
