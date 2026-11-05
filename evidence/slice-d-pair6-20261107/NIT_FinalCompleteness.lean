import NIT_PairComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_FinalCompleteness
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

theorem add_complete (a b : E) (ha : canonE a) (hb : canonE b) :
 ∃ reply, FIo_Native.aspis_core.field.wide_exact.WideExact.add a b=ok reply ∧
 canonE reply ∧ EAdd a b reply := by
 obtain ⟨lo,hlo,clo,vlo⟩ := LPi_TowerValues.qm_add a.c0 b.c0 ha.1 hb.1
 obtain ⟨hi,hhi,chi,vhi⟩ := LPi_TowerValues.qm_add a.c1 b.c1 ha.2 hb.2
 refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,Prod.ext vlo vhi⟩
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,hlo,hhi,bind_tc_ok]

/-- Instantiate both CLOSED field packets on the SAME arguments, thereby
constructing admissible local logs rather than postulating a successful result. -/
theorem local_log (parts powers : Parts) (hp : canonical parts) (hk : canonical powers)
 (kind : Nat) (small : kind<7) (before : E) (hb : canonE before) :
 ∃ l after,cutFinal parts powers kind before l after ∧
 EMul l.mul_a l.mul_b l.product ∧ EAdd l.add_a l.add_b l.reply ∧ canonE after := by
 let power := epick powers kind
 let part := epick parts kind
 obtain ⟨product,hm,cm,vm⟩ := LPi_TowerValues.wide_mul power part
  (epick_canonical powers hk kind) (epick_canonical parts hp kind)
 obtain ⟨reply,ha,ca,va⟩ := add_complete before product hb cm
 let l : Final := ⟨power,part,product,before,product,reply,2,[0,1]⟩
 exact ⟨l,reply,⟨small,hp,hk,hb,cm,ca,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,vm,va,ca⟩

/-- The loop invariant supplies every next local-cut domain. This is constructive
finite log coverage; no final sum/packet equation occurs among its premises. -/
theorem trace_exists (parts powers : Parts) (hp : canonical parts) (hk : canonical powers)
 (fuel : Nat) (s : NHX_FinalLoop.State) (last : s.1.end.val=7)
 (small : s.1.start.val≤7) (hs : canonE s.2) (enough : 7-s.1.start.val<fuel) :
 ∃ out,FinalTrace parts powers fuel s out ∧ canonE out := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
   by_cases active : s.1.start.val<7
   · obtain ⟨l,after,cut,mulLaw,addLaw,canonical⟩ := local_log parts powers hp hk
      s.1.start.val active s.2 hs
     obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
     obtain ⟨out,tail,co⟩ := ih (rest,after) (by simpa only [he] using last)
      (by change rest.start.val≤7;omega) canonical (by change 7-rest.start.val<fuel;omega)
     exact ⟨out,.step fuel s out after l cut mulLaw addLaw rest next tail,co⟩
   · exact ⟨s.2,.done fuel s (by omega),hs⟩

/-- All seven steps, both field laws and the final scalar agree with the exact
emitted loop on arbitrary canonical parts/powers. This is a subchain result. -/
theorem complete (parts powers : Parts) (hp : canonical parts) (hk : canonical powers) :
 ∃ out,FinalTrace parts powers 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) out ∧
 FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize}
  parts powers NHI_Scalar.zero=ok out ∧ canonE out := by
 obtain ⟨out,trace,canonical⟩ := trace_exists parts powers hp hk 8
  ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) rfl
  (by change (0:Nat)≤7;omega) NHI_Scalar.zero_canonical (by change (7:Nat)-0<8;omega)
 exact ⟨out,trace,final_loop parts powers out trace,canonical⟩

#print axioms add_complete
#print axioms local_log
#print axioms trace_exists
#print axioms complete
end AspisR1.NIT_FinalCompleteness
