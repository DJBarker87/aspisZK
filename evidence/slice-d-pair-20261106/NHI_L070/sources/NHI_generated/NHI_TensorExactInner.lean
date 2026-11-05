import NHI_TensorExactCell
import NHI_Reverse
set_option autoImplicit false
noncomputable section
namespace NHI_TensorExactInner
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHI_TensorExactCell
abbrev Rev := NHI_Reverse.Rev
abbrev State := Rev × Slice NQ

def body (w : FIo_Native.weights.Weights) (k n d : Usize) (s : State) :=
 FIo_Native.weights.Weights.tensor_loop0_loop0.body w k n d s.1 s.2

def descend (row : Array NQ 4#usize) (n : Nat) : Nat → Slice NQ → Slice NQ
 | 0,input => input
 | m+1,input => descend row n m (place input m n row)

theorem finite (w : FIo_Native.weights.Weights) (k d n : Usize)
 (hk : k.val<5) (hd : d.val<5) (hn : NHI_TensorDomains.Stage n.val)
 (digitCanon : NHI_CellCanon.array (rowAt w k d hk hd)) (m : Nat)
 (e : Usize) (he : e.val=m) (cap : e.val ≤ n.val) (input : Slice NQ)
 (len : input.val.length=64) (canonical : NHI_CellCanon.slice input) :
 loop (body w k n d) (NHI_Reverse.cursor e,input)=
 ok (w,descend (rowAt w k d hk hd) n.val m input) := by
 induction m generalizing e input with
 | zero =>
  have ez : e=0#usize := UScalar.eq_of_val_eq he
  subst e
  have stop := NHI_Reverse.stop
  unfold NHI_Reverse.next at stop
  have done : body w k n d (NHI_Reverse.cursor 0#usize,input)=ok (.done (w,input)) := by
   simp only [body,FIo_Native.weights.Weights.tensor_loop0_loop0.body,stop,bind_tc_ok]
   rfl
  simp only [loop.eq_def,done,bind_tc_ok,descend]
 | succ m ih =>
  obtain ⟨j,dec,next⟩ := NHI_Reverse.step e (by omega)
  obtain ⟨out,run,co,lo,value⟩ := NHI_TensorExactCell.source w k d n j hk hd hn (by omega)
   input len canonical digitCanon (NHI_Reverse.cursor e) (NHI_Reverse.cursor j) next
  have jv : j.val=m := by omega
  have br : body w k n d (NHI_Reverse.cursor e,input)=ok (.cont (NHI_Reverse.cursor j,out)) := run
  have later := ih j jv (by omega) out lo co
  rw [loop.eq_def,br]
  simpa only [bind_tc_ok,descend,value,jv] using later

/-- Complete emitted reverse-loop value equality, not only canonicality. -/
theorem source (w : FIo_Native.weights.Weights) (k d n : Usize)
 (hk : k.val<5) (hd : d.val<5) (hn : NHI_TensorDomains.Stage n.val)
 (digitCanon : NHI_CellCanon.array (rowAt w k d hk hd))
 (e : Usize) (cap : e.val ≤ n.val) (input : Slice NQ)
 (len : input.val.length=64) (canonical : NHI_CellCanon.slice input) :
 FIo_Native.weights.Weights.tensor_loop0_loop0 (NHI_Reverse.cursor e) w k input n d=
 ok (w,descend (rowAt w k d hk hd) n.val e.val input) :=
 finite w k d n hk hd hn digitCanon e.val e rfl cap input len canonical

#print axioms finite
#print axioms source
end NHI_TensorExactInner
end
