from pathlib import Path
E=Path(__file__).resolve().parent
for tag in 'ABC':
 p=E/f'SDY_Mp{tag}.lean';s=p.read_text()
 pos=s.index('theorem parent')
 # Digest is a separate leaf of the parent proof; bound the nine slices symbolically.
 digest={'A':5,'B':3,'C':4}[tag]
 s=s[:pos]+f'''theorem digest_result : aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children (fin0 id (it 8#usize)).iter.slice) = ok (node {digest}#u8) := by
  unfold aspis_core.r0.merkle.parent_with_digest SDY_Join_digest
  split
  · rfl
  · rename_i h
    exfalso
    apply h
    scalar_tac
#print axioms digest_result

'''+s[pos:]
 s=s.replace('  rw [add_eq 0#usize 1#usize 1#usize rfl]\n  rfl\n#print axioms parent','  rw [add_eq 0#usize 1#usize 1#usize rfl,digest_result]\n  rfl\n#print axioms parent')
 pos=s.index('theorem outerFirst')
 s=s[:pos]+'''theorem range_next (i j : U32) (lt : i.val < 6) (inc : j.val = i.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 {start:=i,«end»:=6#u32} = ok (some i,{start:=j,«end»:=6#u32}) := by
  obtain ⟨v,hv,he⟩ := WP.spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec {start:=i,«end»:=6#u32} lt)
  rcases v with ⟨o,r⟩
  rcases he with ⟨ho,hr,hend⟩
  have hs : r.start = j := UScalar.eq_imp r.start j (by change r.start.val = i.val+1 at hr; omega)
  have rr : r = {start:=j,«end»:=6#u32} := by cases r; simp_all
  simpa only [ho,rr] using hv
#print axioms range_next
'''+s[pos:]
 for name,i in [('outerFirst',0),('outerLast',1)]:
  start=s.index(' := by',s.index('theorem '+name))+len(' := by');end=s.index('\n#print axioms '+name,start)
  proof=s[start:end].replace('  change (do','  rw [range_next '+str(i)+'#u32 '+str(i+1)+'#u32 (by decide) rfl,bind_tc_ok]\n  change (do')
  s=s[:start]+proof+s[end:]
 s=s.replace('exact List.length_replicate _ _','exact List.length_replicate')
 s=s.replace('multiproof.LEAF_BITS,hh]\n  rw [loop.eq_def]','multiproof.LEAF_BITS,hh]\n  simp [Slice.getElem_Nat_eq,Slice.getElem_Usize_eq]\n  rw [loop.eq_def]')
 p.write_text(s)
