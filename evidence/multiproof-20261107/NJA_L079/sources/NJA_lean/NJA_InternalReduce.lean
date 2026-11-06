import NJA_Internal

set_option autoImplicit false
noncomputable section
namespace NJA_InternalReduce
open Aeneas Aeneas.Std Result
open NJA_Internal

theorem fold_bound (xs : List Nat) (b a : Nat) (h : ∀ x∈xs, x≤b) :
 xs.foldl (·+·) a ≤ a+xs.length*b := by
 induction xs generalizing a with
 | nil => simp
 | cons x xs ih =>
   have tail := ih (a+x) (by intro y hy; exact h y (by simp [hy]))
   have head := h x (by simp)
   simp only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
   omega

theorem part_bound (s : State) (canonical : ∀ i, (s i).val<2147483647) :
 part s ≤ 15*2147483647 := by
 unfold part
 have h := fold_bound (List.ofFn (fun i : Fin 15 => (s i.succ).val)) 2147483647 0 (by
   intro x hx
   obtain ⟨i,eq⟩ := List.mem_ofFn.mp hx
   subst x
   exact Nat.le_of_lt (canonical i.succ))
 simpa using h

def argument (s : State) (i : Fin 16) : Nat :=
 if h : i.val=0 then zeroArg s else nonzeroArg s i h

theorem argument_bound (s : State) (i : Fin 16)
 (canonical : ∀ j, (s j).val<2147483647) : argument s i < 2^62 := by
 have partb := part_bound s canonical
 have z := canonical 0
 unfold argument
 split
 · unfold zeroArg
   omega
 · next hi =>
   have shifted := shifted_bound (s i) ⟨i.val-1,by omega⟩
   unfold nonzeroArg
   omega

def word (s : State) (i : Fin 16) : U64 := ⟨BitVec.ofNat 64 (argument s i)⟩

theorem word_value (s : State) (i : Fin 16)
 (canonical : ∀ j, (s j).val<2147483647) : (word s i).val = argument s i := by
 change argument s i % 2^64 = argument s i
 apply Nat.mod_eq_of_lt
 have := argument_bound s i canonical
 omega

theorem argument_model (s : State) (i : Fin 16)
 (canonical : ∀ j, (s j).val<2147483647) :
 (argument s i:K) = R0P.poseidonInternalLinear (fun j => ((s j).val:K)) i := by
 unfold argument
 split
 · next hi =>
   have eq : i=0 := Fin.ext hi
   subst i
   exact zero_model s (canonical 0)
 · next hi => exact nonzero_model s i hi

theorem callee (s : State) (i : Fin 16)
 (canonical : ∀ j, (s j).val<2147483647) : ∃ z : U32,
 AspisR1SelectedMaskProbe.field.M31.reduce_u62 (word s i) = ok z ∧
 z.val<2147483647 ∧ (z.val:K) = R0P.poseidonInternalLinear (fun j => ((s j).val:K)) i := by
 obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.reduce_u62 (word s i)
 refine ⟨z,hz,cz,?_⟩
 rw [vz,word_value s i canonical]
 rw [←argument_model s i canonical]
 simp [K,NJA_Matrix.K,AspisV8R15.ExactTowerBase.M31Exact,ZMod.natCast_mod]

#print axioms fold_bound
#print axioms part_bound
#print axioms argument_bound
#print axioms word_value
#print axioms argument_model
#print axioms callee
end NJA_InternalReduce
end
