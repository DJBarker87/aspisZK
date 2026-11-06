import NLH_PartsState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsValues
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKR_TermTail (Calls Carrier)
def values {zc point mu comp h active} (p : Calls zc point mu comp h active) (i : Fin 9) : NQ :=
 match i.val with
 | 0 => p.eq
 | 1 => p.weighted
 | 2 => p.muH
 | 3 => p.sum
 | 4 => p.mu2
 | 5 => p.inactive
 | 6 => p.inactiveH
 | 7 => p.extra
 | _ => p.out
def snapshot {zc point mu comp h active} (p : Calls zc point mu comp h active) (n : Nat) : Fin 9 → NQ :=
 fun j => if j.val < n then values p j else field.QM31.ZERO
def stage {zc point mu} (child : Carrier)
 (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) (n : Nat) : NLH_PartsState.State :=
 ⟨child,snapshot p n⟩
theorem update {zc point mu comp h active} (p : Calls zc point mu comp h active) (i : Fin 9) :
 (fun j => if j=i then values p i else snapshot p i.val j)=snapshot p (i.val+1) := by
 funext j
 by_cases same : j=i
 · subst j
   simp only [snapshot,if_pos (Nat.lt_succ_self i.val),ite_true]
 · have different : j.val ≠ i.val := by intro h;exact same (Fin.ext h)
   unfold snapshot
   by_cases earlier : j.val < i.val
   · simp only [if_pos earlier,if_neg same,if_pos (show j.val < i.val+1 by omega)]
   · simp only [if_neg earlier,if_neg same,if_neg (show ¬j.val < i.val+1 by omega)]
#print axioms update
end AspisR1.NLH_PartsValues
end
