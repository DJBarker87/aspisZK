from pathlib import Path
E=Path(__file__).resolve().parent
for tag,index in [('A',8),('B',9),('C',10)]:
 p=E/f'SDY_Mp{tag}.lean';s=p.read_text();pos=s.index('theorem formed');end=s.index('\n#print axioms formed',pos)+len('\n#print axioms formed')
 t=f'''abbrev Pred := multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
abbrev PredCall := multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
abbrev ReadIter := core.slice.iter.Iter U32
abbrev AllState := ReadIter × Unit
abbrev AllOut := Bool × ReadIter × Unit
def allBody (s : AllState) : Result (ControlFlow AllState AllOut) := do
  let (item,next) ← core.slice.iter.IteratorSliceIter.next s.1
  match item with
  | none => ok (ControlFlow.done (true,next,s.2))
  | some value =>
    let (holds,p) ← Pred.call_mut s.2 value
    if holds then ok (ControlFlow.cont (next,p)) else ok (ControlFlow.done (false,next,p))
theorem pred_result : PredCall () {index}#u32 = ok (true,()) := by
  unfold PredCall multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut multiproof.LEAF_BITS
  rfl
#print axioms pred_result
theorem all_first : allBody (⟨singleton,0⟩,()) = ok (ControlFlow.cont (⟨singleton,1⟩,())) := by
  unfold allBody
  change (do let (b,p) ← PredCall () {index}#u32; if b then ok (ControlFlow.cont (⟨singleton,1⟩,p)) else ok (ControlFlow.done (false,⟨singleton,1⟩,p))) = _
  rw [pred_result]
  rfl
#print axioms all_first
theorem all_last : allBody (⟨singleton,1⟩,()) = ok (ControlFlow.done (true,⟨singleton,1⟩,())) := by rfl
#print axioms all_last
theorem all_run_last : loop allBody (⟨singleton,1⟩,()) = ok (true,⟨singleton,1⟩,()) := SDY_Loop.done allBody _ _ all_last
#print axioms all_run_last
theorem all_run : loop allBody (⟨singleton,0⟩,()) = ok (true,⟨singleton,1⟩,()) := SDY_Loop.next allBody _ _ _ all_first all_run_last
#print axioms all_run
theorem all_result : core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all Pred ⟨singleton,0⟩ () = ok (true,⟨singleton,1⟩) := by
  change (do let out ← loop allBody (⟨singleton,0⟩,()); ok (out.1,out.2.1)) = _
  rw [all_run]
  rfl
#print axioms all_result
abbrev WinPred := multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
def windows : core.slice.iter.Windows U32 := ⟨singleton,2#usize,0⟩
theorem windows_result : core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all WinPred windows () = ok (true,windows) := by
  unfold core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  rfl
#print axioms windows_result
theorem formed : multiproof.well_formed singleton = ok true := by
  unfold multiproof.well_formed multiproof.MAX_BATCH
  change (do let (b,_) ← core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all WinPred windows ()
             if b then do
               let (b2,_) ← core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all Pred ⟨singleton,0⟩ ()
               ok b2
             else ok false) = _
  rw [windows_result,bind_tc_ok]
  simp only [ite_true]
  rw [all_result]
  rfl
#print axioms formed'''
 s=s[:pos]+t+s[end:];p.write_text(s)
