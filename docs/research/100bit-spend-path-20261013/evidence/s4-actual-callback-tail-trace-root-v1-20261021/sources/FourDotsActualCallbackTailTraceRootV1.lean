import AspisR1FastDotsCurrent.FunsOpsV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualCallbackTailTraceRootV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev QM := AspisR1FastDotsCurrent.aspis_core.field.QM31
abbrev Tail := AspisR1FastDotsCurrent.fast_pairing.EbyKDot
abbrev Closure := AspisR1FastDotsCurrent.fast_dots.four_dots.closure
abbrev StepBy := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
abbrev Callback := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
abbrev BaseLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
abbrev TailLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Successful actual full callback exposes the same base accumulator and
all source calls supplying its three-term extension-field tail. -/
theorem actual_callback_success_base_and_tail
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (value : Wide) (c' : Closure)
    (h : Callback ops (a,g) slot = .ok (value,c')) :
    c'=(a,g) ∧
    ∃ (iter : StepBy) (limbs : Array U64 8#usize) (vals : Array U32 8#usize)
      (optBody : Option Wide) (body : Wide) (tail0 : Tail) (wide28 : Wide)
      (slotOffset start finish : Usize) (bytes : Slice U8) (optQ : Option QM) (q : QM)
      (pushed : core.result.Result Unit Unit × Tail) (u : Unit) (tail2 : Tail) (tailValue : Wide),
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      BaseLoop ops iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      ops.arrayFromFn 8#usize
        (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
        limbs = .ok vals ∧
      ops.wideFromLimbs vals = .ok optBody ∧ core.option.Option.unwrap optBody = .ok body ∧
      ops.ebyKNew = .ok tail0 ∧ Array.index_usize g 28#usize = .ok wide28 ∧
      (slot*120#usize : Result Usize) = .ok slotOffset ∧
      (slotOffset+104#usize : Result Usize) = .ok start ∧
      (slotOffset+120#usize : Result Usize) = .ok finish ∧
      core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        a {start, «end»:=finish} = .ok bytes ∧
      ops.qm31FromBytes bytes = .ok optQ ∧ core.option.Option.unwrap optQ = .ok q ∧
      ops.ebyKPush tail0 wide28 q = .ok pushed ∧
      core.result.Result.unwrap core.fmt.DebugUnit pushed.1 = .ok u ∧
      TailLoop ops {start:=0#usize, «end»:=2#usize} a g slot pushed.2 = .ok tail2 ∧
      ops.ebyKFinish tail2 = .ok tailValue ∧ ops.wideAdd body tailValue = .ok value := by
  unfold Callback at h
  obtain ⟨iter,hstep,hrest⟩ := bind_success _ _ _ h
  obtain ⟨limbs,hbase,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨vals,hvals,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨optBody,hbody,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨body,hunwrap,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨tail0,hnew,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨wide28,hread,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨slotOffset,hmul,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨start,hadd104,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨finish,hadd120,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨bytes,hslice,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨optQ,hparse,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨q,hunq,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨pushed,hpush,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨u,hunpush,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨tail2,htail,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨tailValue,hfinish,hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨sumValue,hadd,hret⟩ := bind_success _ _ _ hrest
  have hp : (sumValue,(a,g))=(value,c') := Result.ok.inj hret
  have hv : sumValue=value := congrArg Prod.fst hp
  have hc : c'=(a,g) := (congrArg Prod.snd hp).symm
  subst sumValue
  exact ⟨hc,iter,limbs,vals,optBody,body,tail0,wide28,slotOffset,start,finish,bytes,optQ,q,
    pushed,u,tail2,tailValue,hstep,hbase,hvals,hbody,hunwrap,hnew,hread,hmul,hadd104,hadd120,
    hslice,hparse,hunq,hpush,hunpush,htail,hfinish,hadd⟩
#print axioms actual_callback_success_base_and_tail
end AspisR1FastDotsActualCallbackTailTraceRootV1
