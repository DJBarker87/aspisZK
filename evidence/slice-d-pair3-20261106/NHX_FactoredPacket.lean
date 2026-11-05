import NHI_CountedLoop
import NHI_ForwardRange
import NHX_FactoredSuffix
import NHM_FactoredDomain
set_option autoImplicit false
namespace NHX_FactoredPacket
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_FactoredPrefix

theorem tail_total (ap0 ap1 : Cells) (side : Usize) (iter : Iter) (weights : Cells)
 (low high : Array NQ 4#usize) (q4 q16 : NQ)
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x)
 (hw : ∀ x∈weights.val,canonE x) (hl : ∀ x∈low.val,canonQ x)
 (hh : ∀ x∈high.val,canonQ x) (h4 : canonQ q4) (h16 : canonQ q16) :
 ∃ out,tail ap0 ap1 side iter weights low high q4 q16=ok (.cont (iter,out)) ∧
 (∀ x∈out.val,canonE x) := by
 obtain ⟨a,b,c,d,hp,ca,cb,cc,cd⟩:=NHX_FactoredCut.prefix_total ap0 ap1 low high ha hb hl hh
 obtain ⟨out,ho,co⟩:=NHX_FactoredSuffix.total ap1 side iter weights q4 q16 a b c d ca cb cc cd hw h4 h16
 refine ⟨out,?_,co⟩
 rw [NHX_FactoredCut.split,hp,bind_tc_ok]
 exact ho

def Inv (s : State) : Prop := s.1.end.val=2 ∧ s.1.start.val≤2 ∧ ∀ x∈s.2.val,canonE x

theorem active (ap0 ap1 : Cells) (extra : Array NQ 2#usize)
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x)
 (he : ∀ x∈extra.val,canonQ x) (s : State) (h : Inv s) (side : Usize) (next : Iter)
 (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some side,next)) :
 ∃ out,body ap0 ap1 extra s=ok (.cont (next,out)) ∧ (∀ x∈out.val,canonE x) := by
 obtain ⟨hend,hbound,hcanon⟩:=h
 obtain ⟨same,last,inc,more⟩:=NHI_RangeProgress.some_next s.1 next side hn
 have bound:side.val<2:=by rw [same];omega
 obtain ⟨q,low,high,q4,q16,hi,hp,cl,ch,c4,c16⟩:=NHM_FactoredDomain.producers extra he side bound
 obtain ⟨out,ho,co⟩:=tail_total ap0 ap1 side next s.2 low high q4 q16 ha hb hcanon cl ch c4 c16
 refine ⟨out,?_,co⟩
 unfold body
 rw [hn]
 simp only [bind_tc_ok]
 change (do
  let q ← Array.index_usize extra side
  let (low,high,q4,q16) ← NHI_FactoredProducers.run q
  tail ap0 ap1 side next s.2 low high q4 q16)=ok (.cont (next,out))
 rw [hi]
 simp only [bind_tc_ok]
 rw [hp]
 simp only [bind_tc_ok]
 exact ho

def initial : State := ({start:=0#usize,«end»:=2#usize},Array.repeat 4#usize NHI_Scalar.zero)
def reference (ap0 ap1 : Cells) (extra : Array NQ 2#usize) :=
 NHI_CountedLoop.unroll (body ap0 ap1 extra) 3 initial

/-- Two source-ordered SAME side packets, with the emitted q^4 call retained.
Canonicality is proved from primitive operands; no child-success premise. -/
theorem source (ap0 ap1 : Cells) (extra : Array NQ 2#usize)
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x)
 (he : ∀ x∈extra.val,canonQ x) :
 ∃ out,FIo_Native.weights.factored_s2_libra_weights ap0 ap1 extra=ok out ∧
 reference ap0 ap1 extra=ok out ∧ (∀ x∈out.val,canonE x) := by
 have ci:∀ x∈initial.2.val,canonE x:=by
  intro x hx
  simp only [initial,Array.repeat,List.mem_replicate] at hx
  rw [hx.2]
  exact NHI_Scalar.zero_canonical
 have h0:Inv initial:=⟨rfl,by change (0:Nat)≤2;omega,ci⟩
 have n0:core.iter.range.IteratorRange.next core.iter.range.StepUsize initial.1=
  ok (some 0#usize,{start:=1#usize,«end»:=2#usize}):=by
  exact NHI_ForwardRange.exact_step initial.1 1#usize (by change (0:Nat)<2;omega) (by change (1:Nat)=0+1;rfl)
 obtain ⟨a,sa,ca⟩:=active ap0 ap1 extra ha hb he initial h0 0#usize _ n0
 let s1:State:=({start:=1#usize,«end»:=2#usize},a)
 have h1:Inv s1:=⟨rfl,by change (1:Nat)≤2;omega,ca⟩
 have n1:core.iter.range.IteratorRange.next core.iter.range.StepUsize s1.1=
  ok (some 1#usize,{start:=2#usize,«end»:=2#usize}):=by
  exact NHI_ForwardRange.exact_step s1.1 2#usize (by change (1:Nat)<2;omega) (by change (2:Nat)=1+1;rfl)
 obtain ⟨b,sb,cb⟩:=active ap0 ap1 extra ha hb he s1 h1 1#usize _ n1
 let s2:State:=({start:=2#usize,«end»:=2#usize},b)
 have stopped:body ap0 ap1 extra s2=ok (.done b):=by
  unfold body
  have dn:core.iter.range.IteratorRange.next core.iter.range.StepUsize s2.1=ok (none,s2.1):=
   NHI_ForwardRange.done s2.1 (by change (2:Nat)≤2;omega)
  rw [dn]
  rfl
 dsimp only [s1,s2] at sb stopped
 have bodies:(fun s:State=>FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra s.1 s.2)=body ap0 ap1 extra:=
  funext (fun s=>NHM_FactoredPrefix.source ap0 ap1 extra s)
 refine ⟨b,?_,?_,cb⟩
 · unfold FIo_Native.weights.factored_s2_libra_weights FIo_Native.weights.factored_s2_libra_weights_loop
   rw [bodies]
   change loop (body ap0 ap1 extra) initial=ok b
   rw [loop.eq_def,sa]
   simp only [bind_tc_ok]
   rw [loop.eq_def,sb]
   simp only [bind_tc_ok]
   rw [loop.eq_def,stopped]
 · simp only [reference,NHI_CountedLoop.unroll,sa,bind_tc_ok,sb,stopped]

#print axioms tail_total
#print axioms active
#print axioms source
end NHX_FactoredPacket
