import NDO_JHa_DotContext
import NDO_JHa_DotOuterStepMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotOuterMeaning
open Aeneas Aeneas.Std Result ControlFlow
open JFv_TX2_ArrayMeaning (cell)
abbrev State := JFs_TX2_Iterator.Iter × Array U64 8#usize

def sum (d : JHa_DotContext.Data) (j : Fin 8) : Nat → Nat
  | 0 => 0
  | n+1 => sum d j n+JHa_DotOuterStepMeaning.batch d j (4*n)

def Inv (d : JHa_DotContext.Data) (s : State) : Prop :=
  ∃ n : Nat, n≤7 ∧ s.1.step_by.val=4 ∧ s.1.iter.end.val=26 ∧
    s.1.iter.start.val=min (4*n) 26 ∧ JFs_TX2_FoldEight.Bound s.2 n ∧
    ∀ j : Fin 8, (cell s.2 j).val=sum d j n

theorem source (d : JHa_DotContext.Data) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      d.q JFr_TX2_FirstLane.native
      (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) (Array.repeat 8#usize 0#u64)=ok out ∧
      JFs_TX2_FoldEight.Bound out 7 ∧ ∀ j : Fin 8, (cell out j).val=sum d j 7 := by
  have spec : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      d.q JFr_TX2_FirstLane.native
      (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) (Array.repeat 8#usize 0#u64)
      ⦃ out => JFs_TX2_FoldEight.Bound out 7 ∧ ∀ j : Fin 8, (cell out j).val=sum d j 7 ⦄ := by
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0
    refine loop.spec_decr_nat (fun s : State => 26-s.1.iter.start.val) (Inv d) _
      (fun (r,s) => FIp_NativeDots.fast_dots.four_dots_one_loop0.body
        d.q JFr_TX2_FirstLane.native
        (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) r s)
      (JFs_TX2_Iterator.value 0,Array.repeat 8#usize 0#u64) ?_ ?_
    · rintro ⟨r,s⟩ ⟨n,hn,step,finish,start,bound,values⟩
      dsimp only at step finish start bound values ⊢
      by_cases active : r.iter.start.val < r.iter.end.val
      · have lt : n<7 := by omega
        have actual : r.iter.start.val=4*n := by omega
        obtain ⟨next,out,run,inc,he,step',bo,vo⟩ := JHa_DotOuterStepMeaning.source d r s n lt step finish active bound
        rw [run,WP.spec_ok]
        change Inv d (next,out) ∧ 26-next.iter.start.val < 26-r.iter.start.val
        refine ⟨⟨n+1,by omega,step',he,?_,bo,?_⟩,?_⟩
        · dsimp only;omega
        · intro j
          change (cell out j).val=sum d j (n+1)
          rw [vo j,values j,actual,sum]
        · omega
      · rw [JFs_TX2_OuterStep.body]
        simp only [JFs_TX2_OuterStep.step,JFs_TX2_Iterator.stopped r (by omega),
          bind_tc_ok,Aeneas.Std.uncurry,WP.spec_ok]
        have same : n=7 := by omega
        simpa only [same] using And.intro bound values
    · refine ⟨0,by omega,rfl,rfl,rfl,?_,?_⟩
      · intro x hx
        have same : x=0#u64 := (List.mem_replicate.mp hx).2
        subst x
        simp
      · intro j
        fin_cases j <;> rfl
  exact WP.spec_imp_exists spec
#print axioms source
end AspisR1.JHa_DotOuterMeaning
end
