import FIo_ArrayBack
import FIo_GroupCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_PowersCanonical
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
abbrev State (N : Usize) := Array NE N × NE × Usize
def Inv {N : Usize} (s : State N) : Prop := FIo_ArrayCanon.Holds s.1 ∧ FIo_WideValues.Canon s.2.1
def measure {N : Usize} (s : State N) : Nat := N.val-s.2.2.val

theorem step {N : Usize} (x : NE) (hx : FIo_WideValues.Canon x)
    (s : State N) (inv : Inv s) (out : ControlFlow (State N) (Array NE N))
    (run : FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2=ok out) :
    match out with
    | .done a => FIo_ArrayCanon.Holds a
    | .cont t => Inv t ∧ measure t<measure s := by
  rcases s with ⟨a,p,i⟩
  unfold FIo_Native.weights.powers_loop.body at run
  split at run
  · rename_i more
    obtain ⟨⟨old,back⟩,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have hc := FIo_ArrayBack.canonical a i old back hb inv.1 p inv.2
    split at run
    · have same : done (back p)=out := Result.ok.inj run
      subst out
      exact hc
    · obtain ⟨next,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have same : cont (back p,next,Usize.wrapping_add i 1#usize)=out := Result.ok.inj run
      subst out
      have cn := (FIo_WideMulValues.mul p x next inv.2 hx hn).1
      refine ⟨⟨hc,cn⟩,?_⟩
      have inc : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
        rw [Usize.wrapping_add_val_eq]
        change (i.val+1)%UScalar.size .Usize=i.val+1
        apply Nat.mod_eq_of_lt
        apply lt_of_le_of_lt (show i.val+1≤N.val from by scalar_tac)
        simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using N.bv.isLt
      simp only [measure,inc]
      scalar_tac
  · have same : done a=out := Result.ok.inj run
    subst out
    exact inv.1

theorem loop_canonical {N : Usize} (x : NE) (hx : FIo_WideValues.Canon x)
    (a result : Array NE N) (p : NE) (i : Usize) (inv : Inv (a,p,i))
    (run : FIo_Native.weights.powers_loop x a p i=ok result) : FIo_ArrayCanon.Holds result := by
  exact FIo_LoopInvariant.preserve
    (fun s : State N => FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2)
    Inv FIo_ArrayCanon.Holds measure
    (fun s h out hr => by cases out <;> exact step x hx s h _ hr)
    (a,p,i) result inv run

theorem canonical (N : Usize) (x : NE) (result : Array NE N) (hx : FIo_WideValues.Canon x)
    (run : FIo_Native.weights.powers N x=ok result) : FIo_ArrayCanon.Holds result := by
  exact loop_canonical x hx _ result _ _ ⟨FIo_GroupCanonical.zeros N,FIo_Constants.one.1⟩ run

#print axioms step
#print axioms loop_canonical
#print axioms canonical
end AspisR1.FIo_PowersCanonical
end
