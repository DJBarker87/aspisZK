import RPt_FJi_OuterTerm
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_OuterStep
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations
open FJf_U64Array (cell)
abbrev State := FJi_OuterTerm.Iter × Sums

def sum (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (j : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sum q g slot j n+FJi_OuterTerm.batch q g slot j (4*n)

def Inv (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (s : State) : Prop :=
  ∃ n : Nat,n ≤ 7 ∧ s.1.step_by.val=4 ∧ s.1.iter.end.val=26 ∧
    s.1.iter.start.val=min (4*n) 26 ∧ JFs_TX2_FoldEight.Bound s.2 n ∧
    ∀ j : Fin 8,(cell s.2 j.val).val=sum q g slot j.val n

def Post (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : Sums) : Prop :=
  JFs_TX2_FoldEight.Bound out 7 ∧ ∀ j : Fin 8,(cell out j.val).val=sum q g slot j.val 7

def measure (s : State) : Nat := 26-s.1.iter.start.val

theorem step (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (s : State) (inv : Inv q g slot s) (out : ControlFlow State Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot s.1 s.2=ok out) :
    match out with
    | .done result => Post q g slot result
    | .cont next => Inv q g slot next ∧ measure next < measure s := by
  rcases s with ⟨iter,limbs⟩
  rcases inv with ⟨n,hn,hstep,finish,start,bound,values⟩
  dsimp only at hn hstep finish start bound values
  by_cases active : iter.iter.start.val < iter.iter.end.val
  · have lt : n < 7 := by omega
    have actual : iter.iter.start.val=4*n := by omega
    obtain ⟨next,result,same,inc,ending,stepped,bo,vo⟩ :=
      FJi_OuterTerm.value q g slot iter limbs n lt hstep finish active bound out run
    subst out
    refine ⟨⟨n+1,by omega,stepped,ending,?_,bo,?_⟩,?_⟩
    · dsimp only;omega
    · intro j
      change (cell result j.val).val=sum q g slot j.val (n+1)
      rw [vo j,values j,actual,sum]
    · dsimp only [measure];omega
  · rw [JFs_TX2_OuterStep.body] at run
    simp only [JFs_TX2_OuterStep.step,JFs_TX2_Iterator.stopped iter (by omega),
      bind_tc_ok,Aeneas.Std.uncurry] at run
    cases Result.ok.inj run
    have same : n=7 := by omega
    simpa only [Post,same] using And.intro bound values
#print axioms step
end AspisR1.FJi_OuterStep
end
