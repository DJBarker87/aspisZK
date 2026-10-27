from pathlib import Path
E=Path(__file__).resolve().parent
for tag,index,x in [('A',8,2),('B',9,3),('C',10,4)]:
 p=E/f'SDY_Mp{tag}.lean';s=p.read_text()
 s=s.replace('ok (.cont','ok (ControlFlow.cont').replace('ok (.done','ok (ControlFlow.done').replace('(.Eight,','(multiproof.Arity.Eight,')
 for j in [1,2]:s=s.replace(f'{{start:={j}#u32,«end»:=6#u32}},a,x,v,n,offset,p',f'({{start:={j}#u32,«end»:=6#u32}} : core.ops.range.Range U32),a,x,v,n,offset,p')
 s=s.replace('  rw [inner]\n  rfl','  rw [inner]\n  simp only [bind_tc_ok]\n  rw [add_eq 0#usize 1#usize 1#usize rfl]\n  rfl')
 s=s.replace('    simp [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.get,nodes,SDY_Slice.nodes,Slice.length]','    unfold core.slice.Slice.get core.slice.index.SliceIndexRangeUsizeSlice core.slice.index.SliceIndexRangeUsizeSlice.get\n    simp only [nodes,SDY_Slice.nodes,Slice.length,List.length_replicate]\n    rfl')
 s=s.replace('  simp [multiproof.index_at,outidx]\n  rw [hn]\n  rfl','''  have hi : multiproof.index_at outidx 0#usize = ok 1#u32 := by rfl
  have hs : 1#u32 >>> 3#i32 = ok 0#u32 := by rfl
  have hm : 1#u32 &&& 7#u32 = 1#u32 := by rfl
  have hc : UScalar.cast .Usize 1#u32 = 1#usize := by scalar_tac
  rw [hi,bind_tc_ok,hs,bind_tc_ok]
  simp only [if_pos rfl,hm,hc,lift,bind_tc_ok]
  simp only [if_neg (by decide : 1#usize ≠ 0#usize)]
  rw [hn]
  rfl''')
 s=s.replace('  unfold multiproof.well_formed\n','  have hh : 1#u32 <<< 18#u32 = ok 262144#u32 := by rfl\n  unfold multiproof.well_formed\n')
 s=s.replace('multiproof.LEAF_BITS]\n  rw [loop.eq_def]','multiproof.LEAF_BITS,hh]\n  rw [loop.eq_def]')
 # Replace the top-level conversion with separately proved guards.
 start=s.index(' := by',s.index('theorem emitted'))+len(' := by');end=s.index('\n#print axioms emitted',start)
 s=s[:start]+'''\n  have hg : Slice.len nodes = 224#usize := by
    apply UScalar.eq_of_val_eq
    change (List.replicate 224 _).length = 224
    exact List.length_replicate _ _
  have hm : 224#usize % 32#usize = ok 0#usize := by rfl
  have hl : multiproof.Arity.levels .Eight = ok 6#u32 := by
    unfold multiproof.Arity.levels multiproof.Arity.bits multiproof.LEAF_BITS
    rfl
  have hx : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx {«end»:=1#usize} = ok singleton := by rfl
  unfold multiproof.verify_in_place
  simp only [multiproof.MAX_BATCH]
  simp only [show (1#usize = 0#usize) = False from propext (by decide),show (1#usize > 16#usize) = False from propext (by decide),ite_false]
  rw [hx,bind_tc_ok,formed,bind_tc_ok]
  simp only [ite_true]
  rw [hg,hm,bind_tc_ok]
  simp only [show (0#usize != 0#usize) = false from rfl, Bool.false_eq_true,ite_false]
  rw [hl,bind_tc_ok,orun]
  rfl'''+s[end:]
 p.write_text(s)
