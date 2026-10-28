import NDO_JGw_DotOuterActive
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_DotOuter
open Aeneas Aeneas.Std Result ControlFlow
abbrev State := JFs_TX2_Iterator.Iter × Array U64 8#usize

def Inv (s : State) : Prop := ∃ n : Nat, n≤7 ∧ s.1.step_by.val=4 ∧
  s.1.iter.end.val=26 ∧ s.1.iter.start.val=min (4*n) 26 ∧ JFs_TX2_FoldEight.Bound s.2 n

theorem source (q : Array U8 608#usize) (slot : Fin 4)
    (scalars : Fin 26 → U32)
    (reads : ∀ term, JFr_TX2_ScalarRead.read q
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))=ok (scalars term))
    (canonical : ∀ term, (scalars term).val<2147483647) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q JFr_TX2_FirstLane.native
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) (Array.repeat 8#usize 0#u64)=ok out ∧
      JFs_TX2_FoldEight.Bound out 7 := by
  have spec : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q JFr_TX2_FirstLane.native
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) (Array.repeat 8#usize 0#u64)
      ⦃ out => JFs_TX2_FoldEight.Bound out 7 ⦄ := by
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0
    refine loop.spec_decr_nat (fun s : State => 26-s.1.iter.start.val) Inv
      (fun out => JFs_TX2_FoldEight.Bound out 7)
      (fun (r,s) => FIp_NativeDots.fast_dots.four_dots_one_loop0.body
        q JFr_TX2_FirstLane.native
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) r s)
      (JFs_TX2_Iterator.value 0,Array.repeat 8#usize 0#u64) ?_ ?_
    · rintro ⟨r,s⟩ ⟨n,hn,step,finish,start,bound⟩
      dsimp only at step finish start bound ⊢
      by_cases active : r.iter.start.val < r.iter.end.val
      · have lt : n<7 := by omega
        obtain ⟨next,out,run,inc,he,step',bo⟩ := JGw_DotOuterActive.source q slot scalars reads canonical r s n lt step finish active bound
        rw [run,WP.spec_ok]
        change Inv (next,out) ∧ 26-next.iter.start.val < 26-r.iter.start.val
        refine ⟨⟨n+1,by omega,step',he,?_,bo⟩,?_⟩
        · dsimp only
          omega
        · omega
      · rw [JFs_TX2_OuterStep.body]
        simp only [JFs_TX2_OuterStep.step,JFs_TX2_Iterator.stopped r (by omega),
          bind_tc_ok,Aeneas.Std.uncurry,WP.spec_ok]
        have same : n=7 := by omega
        simpa only [same] using bound
    · refine ⟨0,by omega,rfl,rfl,rfl,?_⟩
      intro x hx
      change x∈List.replicate 8 (0#u64) at hx
      have same : x=0#u64 := (List.mem_replicate.mp hx).2
      subst x
      simp
  exact WP.spec_imp_exists spec

#print axioms source
end AspisR1.JGw_DotOuter
end
