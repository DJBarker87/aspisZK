import FJl_InnerReads
import FJi_OuterValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_OuterReads
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations
open FJl_InnerReads (Read)
abbrev State := FJi_OuterTerm.Iter × Sums
/-- Provenance of every scalar read through all seven actual source groups. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q g slot (Array.repeat 8#usize 0#u64)=ok out) :
    ∀ n,n < 26 → Read q slot n := by
  let inv : State → Prop := fun s=>s.1.step_by.val=4 ∧ s.1.iter.end.val=26 ∧ s.1.iter.start.val ≤ 26 ∧
    ∀ n,n < s.1.iter.start.val → Read q slot n
  let post : Sums → Prop := fun _=>∀ n,n < 26 → Read q slot n
  apply FIo_LoopInvariant.preserve
    (fun s : State=>FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot s.1 s.2)
    inv post (fun s=>26-s.1.iter.start.val) ?_ (JFs_TX2_Iterator.value 0,Array.repeat 8#usize 0#u64) out ?_ run
  · intro s h result called
    rcases s with ⟨iter,limbs⟩
    obtain ⟨hstep,he,upper,reads⟩ := h
    dsimp only at hstep he upper reads
    by_cases active : iter.iter.start.val < iter.iter.end.val
    · obtain ⟨next,hn,inc,ending,stepEq⟩ := JFs_TX2_Iterator.next iter hstep active
      obtain ⟨end4,stop,ha,hm,ordered,small,width,vs⟩ := JFs_TX2_BatchWindow.source iter.iter.start (by omega)
      rw [JFs_TX2_OuterStep.body] at called
      simp only [JFs_TX2_OuterStep.step,hn,bind_tc_ok,Aeneas.Std.uncurry,ha,hm] at called
      obtain ⟨sums,hs,called⟩ := Port3_PushFrame.bind_success _ _ _ called
      obtain ⟨limbs1,hl,called⟩ := Port3_PushFrame.bind_success _ _ _ called
      cases Result.ok.inj called
      have group := FJl_InnerReads.value q g slot {start:=iter.iter.start,«end»:=stop}
        (Array.repeat 8#usize 0#u64) sums ordered small hs
      dsimp only at inc ending group vs
      dsimp only [inv]
      refine ⟨⟨stepEq,by simpa only [ending] using he,?_,?_⟩,?_⟩
      · omega
      · intro n hn'
        by_cases old : n < iter.iter.start.val
        · exact reads n old
        · exact group n (by omega) (by omega)
      · omega
    · rw [JFs_TX2_OuterStep.body] at called
      simp only [JFs_TX2_OuterStep.step,JFs_TX2_Iterator.stopped iter (by omega),
        bind_tc_ok,Aeneas.Std.uncurry] at called
      cases Result.ok.inj called
      dsimp only [post]
      intro n hn
      exact reads n (by omega)
  · dsimp only [inv]
    refine ⟨rfl,rfl,by decide,?_⟩
    intro n hn
    change n < 0 at hn
    omega
#print axioms value
end AspisR1.FJl_OuterReads
end
