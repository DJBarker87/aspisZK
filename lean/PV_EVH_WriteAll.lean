import PV_EVH_LiteralDiagnostics
set_option autoImplicit false
namespace PV_EVH_WriteAll
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes NativeEvent)

/-- std1.94.1 Write::write_all control. Writer, io::Error classification/drop,
WRITE_ALL_EOF construction, and oversize indexing panic remain source-binding
obligations. Exhaustion is a prefix, not a Rust io::Error. -/
def run {E : Type} (write : Bytes → Q (Except E Nat)) (dropError : E → Q Unit)
    (interrupted : E → Bool) (writeZero : E) (oversize : Q (Except E Unit)) :
    Nat → Bytes → Q (Except E Unit)
  | 0, buf => if buf = [] then pure (.ok ()) else fun w => ⟨.exhausted,w,[]⟩
  | fuel+1, buf => if buf = [] then pure (.ok ()) else do
      let r ← write buf
      match r with
      | .ok n =>
        if n = 0 then pure (.error writeZero)
        else if n ≤ buf.length then run write dropError interrupted writeZero oversize fuel (buf.drop n)
        else oversize
      | .error e =>
        if interrupted e then do
          let _ ← dropError e
          run write dropError interrupted writeZero oversize fuel buf
        else pure (.error e)

theorem empty {E : Type} (write : Bytes → Q (Except E Nat)) (dropError : E → Q Unit)
    (interrupted : E → Bool) (writeZero : E) (oversize : Q (Except E Unit)) (fuel : Nat) :
    run write dropError interrupted writeZero oversize fuel [] = pure (.ok ()) := by
  cases fuel <;> simp only [run,if_pos rfl]

/-- An EINTR owns an error value whose destructor runs before retry. This is
not a silent retry or an infallible stderr assertion. -/
theorem interrupted_drop {E : Type} (write : Bytes → Q (Except E Nat))
    (dropError : E → Q Unit) (interrupted : E → Bool) (writeZero : E)
    (oversize : Q (Except E Unit)) (fuel : Nat) (buf : Bytes) (w : State) (e : E)
    (hb : buf ≠ []) (hr : (write buf w).outcome = .returned (.ok (.error e)))
    (he : interrupted e = true) :
    run write dropError interrupted writeZero oversize (fuel+1) buf w =
      let next := (do let _ ← dropError e
                     run write dropError interrupted writeZero oversize fuel buf)
      let r := next (write buf w).state
      ⟨r.outcome,r.state,(write buf w).events ++ r.events⟩ := by
  simp only [run,if_neg hb,Bind.bind,PV_EVH_Runtime.bind,hr,he,if_true]

#print axioms empty
#print axioms interrupted_drop
end PV_EVH_WriteAll
