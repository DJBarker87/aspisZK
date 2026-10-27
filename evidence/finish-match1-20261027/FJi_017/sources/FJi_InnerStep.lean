import FJi_TermValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_InnerStep
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations FJi_Inputs
open FJf_U64Array (cell)
abbrev State := FIo_RangeNext.Range × Sums
/-- A symbolic sum; never expanded into 26 concrete reduction steps. -/
def sum (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (j base : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sum q g slot j base n+product q g slot j (base+n)

def Inv (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (base stop : Nat) (seed : Sums) (t : State) : Prop :=
  t.1.end.val=stop ∧ base ≤ t.1.start.val ∧ t.1.start.val ≤ stop ∧
    ∀ j,j < 8 → (cell t.2 j).val=(cell seed j).val+sum q g slot j base (t.1.start.val-base)

def Post (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (base stop : Nat) (seed out : Sums) : Prop :=
  ∀ j,j < 8 → (cell out j).val=(cell seed j).val+sum q g slot j base (stop-base)

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (base stop : Nat) (seed : Sums) (t : State) (small : stop ≤ 26)
    (inv : Inv q g slot base stop seed t) (out : ControlFlow State Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot t.1 t.2=ok out) :
    match out with
    | .done f => Post q g slot base stop seed f
    | .cont next => Inv q g slot base stop seed next ∧ measure next < measure t := by
  rcases t with ⟨iter,s⟩
  rcases inv with ⟨he,hbase,hstop,values⟩
  cases out with
  | done f =>
    obtain ⟨stop',rfl⟩ := FJi_TermValue.done q g slot iter s f run
    have ending : iter.start.val=stop := by omega
    intro j hj
    rw [←ending]
    exact values j hj
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨ending,inc,active,hv⟩ := FJi_TermValue.value q g slot iter cursor s f (by omega) run
    refine ⟨⟨by rw [ending];exact he,by omega,by omega,?_⟩,?_⟩
    · intro j hj
      rw [hv j hj,values j hj,show cursor.start.val-base=(iter.start.val-base)+1 by omega,sum]
      rw [show base+(iter.start.val-base)=iter.start.val by omega,Nat.add_assoc]
    · simp only [measure,ending,inc];omega
#print axioms step
end AspisR1.FJi_InnerStep
end
