import NJA_InternalReduce

set_option autoImplicit false
namespace NJE_SumStage
open Aeneas Aeneas.Std

theorem prefix_fold (xs : List Nat) (states : Nat → Nat) (start : states 0=0)
    (next : ∀ i (h : i<xs.length), states (i+1)=states i+xs[i])
    (n : Nat) (bound : n≤xs.length) :
    states n=(xs.take n).foldl (·+·) 0 := by
 induction n with
 | zero => simpa using start
 | succ n ih =>
   have h : n<xs.length := by omega
   rw [next n h,ih (by omega),List.take_succ_eq_append_getElem h]
   simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]

def Cut (input : NJA_Internal.State) (states : Nat → Nat) : Prop :=
 states 0=0 ∧ ∀ i : Fin 15,
   states (i.val+1)=states i.val+(input i.succ).val

theorem complete (input : NJA_Internal.State) (states : Nat → Nat)
    (cut : Cut input states) : states 15=NJA_Internal.part input := by
 let xs := List.ofFn (fun i : Fin 15 => (input i.succ).val)
 have next : ∀ i (h : i<xs.length), states (i+1)=states i+xs[i] := by
   intro i h
   have hi : i<15 := by simpa only [xs,List.length_ofFn] using h
   change states (i+1)=states i+(List.ofFn (fun j : Fin 15 => (input j.succ).val))[i]
   rw [List.getElem_ofFn]
   exact cut.2 ⟨i,hi⟩
 have final := prefix_fold xs states cut.1 next 15 (by simp [xs])
 have len : xs.length=15 := List.length_ofFn
 rw [←len,List.take_length] at final
 exact final

theorem native_domains (input : NJA_Internal.State) (states : Nat → Nat)
    (cut : Cut input states) (canonical : ∀ i, (input i).val<2147483647)
    (n : Nat) (bound : n≤15) : states n≤n*2147483647 := by
 induction n with
 | zero => simp [cut.1]
 | succ n ih =>
   have hn : n<15 := by omega
   rw [cut.2 ⟨n,hn⟩]
   have before := ih (by omega)
   have term := canonical (⟨n,hn⟩:Fin 15).succ
   simp only [Nat.add_mul,Nat.one_mul]
   omega

#print prefix_fold
#print axioms prefix_fold
#print complete
#print axioms complete
#print native_domains
#print axioms native_domains
end NJE_SumStage
