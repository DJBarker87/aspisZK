import PV_DIAG11_Execution
set_option autoImplicit false
namespace PV_DIAG11

/-! Rust 1.94.1 std::io::Write::write_all branch interpreter.
Fuel bounds observations, NOT source termination: zero fuel on nonempty input
is a divergent finite prefix. Every write call's own effects are retained.
The primitive must implement the Write contract (including count <= length).
An invalid count exposes a panic rather than saturating the slice operation. -/
inductive IoError where | interrupted | writeZero | other (code : Nat)
 deriving DecidableEq, Repr
def writeAll {V : Type} (write : List UInt8 → Run V IoError Nat) :
 Nat → List UInt8 → Run V IoError Unit
 | _,[] => ret ()
 | 0,_::_ => ⟨[],.diverge⟩
 | fuel+1,buf@(_::_) =>
   let r := write buf
   match r.exit with
   | .ok 0 => ⟨r.events,.error .writeZero⟩
   | .ok (n+1) => if n+1 ≤ buf.length then pre r.events (writeAll write fuel (buf.drop (n+1))) else ⟨r.events,.panic⟩
   | .error .interrupted => pre r.events (writeAll write fuel buf)
   | .error e => ⟨r.events,.error e⟩
   | .panic => ⟨r.events,.panic⟩ | .oom => ⟨r.events,.oom⟩
   | .abort => ⟨r.events,.abort⟩ | .diverge => ⟨r.events,.diverge⟩

theorem writeAll_empty {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) : writeAll w fuel []=ret () := by cases fuel <;> rfl
#print axioms writeAll_empty
theorem writeAll_prefix_cut {V : Type} (w : List UInt8 → Run V IoError Nat) (b : UInt8) (bs : List UInt8) : writeAll w 0 (b::bs)=⟨[],.diverge⟩ := rfl
#print axioms writeAll_prefix_cut
theorem writeAll_zero {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.ok 0⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.error .writeZero⟩ := by simp only [writeAll,h]
#print axioms writeAll_zero
theorem writeAll_interrupted {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.error .interrupted⟩) : writeAll w (fuel+1) (b::bs)=pre es (writeAll w fuel (b::bs)) := by simp only [writeAll,h]
#print axioms writeAll_interrupted
theorem writeAll_other_error {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel code : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.error (.other code)⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.error (.other code)⟩ := by simp only [writeAll,h]
#print axioms writeAll_other_error
theorem writeAll_oversize {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel n : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.ok (n+1)⟩) (bad : ¬ n+1 ≤ (b::bs).length) : writeAll w (fuel+1) (b::bs)=⟨es,.panic⟩ := by simp only [writeAll,h,if_neg bad]
#print axioms writeAll_oversize
theorem writeAll_progress {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel n : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.ok (n+1)⟩) (bound : n+1 ≤ (b::bs).length) : writeAll w (fuel+1) (b::bs)=pre es (writeAll w fuel ((b::bs).drop (n+1))) := by simp only [writeAll,h,if_pos bound]
#print axioms writeAll_progress
theorem writeAll_panic {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.panic⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.panic⟩ := by simp only [writeAll,h]
#print axioms writeAll_panic
theorem writeAll_oom {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.oom⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.oom⟩ := by simp only [writeAll,h]
#print axioms writeAll_oom
theorem writeAll_abort {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.abort⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.abort⟩ := by simp only [writeAll,h]
#print axioms writeAll_abort
theorem writeAll_diverge {V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.diverge⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.diverge⟩ := by simp only [writeAll,h]
#print axioms writeAll_diverge
end PV_DIAG11
