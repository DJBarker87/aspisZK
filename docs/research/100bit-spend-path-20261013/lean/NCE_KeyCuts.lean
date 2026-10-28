import NCE_OpeningRead
import NBI_Sort
import NBJ_Keys

set_option autoImplicit false
namespace AspisR1.NCE_KeyCuts
open Aeneas Aeneas.Std Result
open NCE_OpeningCuts

structure KeyState where
  caller : Carrier
  keys : Nat → U64
  cursor : Nat
  batch : Nat
  kind : Nat

def count (s : KeyState) : Nat := if s.batch = 0 then 10 else 12
def lo (s : KeyState) : Nat := if s.batch = 0 then 0 else 10

def canonical (s : KeyState) : Prop :=
  ∀ j, j < 22 → s.caller.prepared.queries.val[j]!.val < 262144

def word (s : KeyState) (j : Nat) : U64 :=
  MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries s.caller.prepared.queries)
    s.batch s.kind (lo s+j)

/-- One raw-query read, packing and key store, with an arbitrary observed
outside key coordinate. The SAME Prepared/proof/scratch/log is unchanged.
Canonical raw-query provenance remains the named NBR_/NBS_ caller obligation.
No sorted array or full producer equality is a hypothesis. -/
def NCE_Native_KeysWrite (native : KeyState → KeyState) : Prop :=
  ∀ s, s.batch < 2 → s.kind < 3 → s.cursor < count s → canonical s →
    (native s).caller = s.caller ∧ (native s).batch = s.batch ∧
    (native s).kind = s.kind ∧ (native s).cursor = s.cursor+1 ∧
    ((native s).keys s.cursor).val =
      256 * (if s.kind = 2 then s.caller.prepared.queries.val[lo s+s.cursor]!.val/4
        else s.caller.prepared.queries.val[lo s+s.cursor]!.val) + s.cursor ∧
    (∀ k, k ≠ s.cursor → (native s).keys k = s.keys k)

/-- The natural native packing law selects the installed U64 word using the
existing NBI theorem. No modulo weakening or hidden canonicality assumption. -/
theorem step_eq (native : KeyState → KeyState) (cut : NCE_Native_KeysWrite native)
    (s : KeyState) (batch : s.batch < 2) (kind : s.kind < 3)
    (active : s.cursor < count s) (queries : canonical s) :
    native s = {s with keys := NBE_KeyLoop.write (word s) s.keys s.cursor, cursor := s.cursor+1} := by
  obtain ⟨caller,b,k,cursor,value,outside⟩ := cut s batch kind active queries
  have index : lo s+s.cursor < 22 := by
    by_cases first : s.batch = 0 <;> simp_all [lo,count] <;> omega
  have packed := NBI_Keys.packed_word s.caller.prepared.queries s.batch s.kind s.cursor
    active (queries _ index)
  have selected : (native s).keys s.cursor = word s s.cursor := by
    apply UScalar.eq_of_val_eq
    exact value.trans packed.symm
  have keys : (native s).keys = NBE_KeyLoop.write (word s) s.keys s.cursor := by
    funext j
    by_cases hit : j = s.cursor
    · subst j
      simpa only [NBE_KeyLoop.write,ite_true] using selected
    · simpa only [NBE_KeyLoop.write,if_neg hit] using outside j hit
  cases s with
  | mk sc sk si sb st =>
    cases h : native (KeyState.mk sc sk si sb st) with
    | mk nc nk ni nb nt =>
      simp only [h] at caller b k cursor keys
      cases caller
      cases b
      cases k
      cases cursor
      cases keys
      rfl

/-- The source fill continuation consumes each previous native poststate. -/
def fill (native : KeyState → KeyState) : Nat → KeyState → KeyState
  | 0,s => s
  | fuel+1,s => fill native fuel (native s)

/-- Complete fill from ONE-step native key cuts. Existing NBE fill semantics
are reused, including the zero/unwritten suffix when that initialization is
supplied separately. A native zero-allocation/initializer cut remains open. -/
theorem fill_eq (native : KeyState → KeyState) (cut : NCE_Native_KeysWrite native)
    (fuel : Nat) (s : KeyState) (batch : s.batch < 2) (kind : s.kind < 3)
    (queries : canonical s) (span : s.cursor+fuel ≤ count s) :
    fill native fuel s = {s with keys := NBE_KeyLoop.fill (word s) fuel s.cursor s.keys, cursor := s.cursor+fuel} := by
  induction fuel generalizing s with
  | zero => simp only [fill,NBE_KeyLoop.fill,Nat.add_zero]
  | succ fuel ih =>
    have active : s.cursor < count s := by omega
    rw [fill,step_eq native cut s batch kind active queries]
    let next : KeyState := {s with keys := NBE_KeyLoop.write (word s) s.keys s.cursor, cursor := s.cursor+1}
    have nextSpan : next.cursor+fuel ≤ count next := by
      change s.cursor+1+fuel ≤ count s
      omega
    have tail := ih next batch kind queries nextSpan
    rw [tail]
    have cursor : s.cursor+1+fuel = s.cursor+(fuel+1) := by omega
    simp only [next,NBE_KeyLoop.fill,cursor] <;> rfl

/-- Arbitrary-coordinate frame and produced values consume NBE's existing
full fill law. All surrounding keys remain arbitrary and unchanged. -/
theorem fill_values (native : KeyState → KeyState) (cut : NCE_Native_KeysWrite native)
    (fuel : Nat) (s : KeyState) (batch : s.batch < 2) (kind : s.kind < 3)
    (queries : canonical s) (span : s.cursor+fuel ≤ count s) (k : Nat) :
    (fill native fuel s).keys k =
      if s.cursor ≤ k ∧ k < s.cursor+fuel then word s k else s.keys k := by
  rw [fill_eq native cut fuel s batch kind queries span]
  exact NBE_KeyLoop.fill_values (word s) s.keys fuel s.cursor k

#print axioms step_eq
#print axioms fill_eq
#print axioms fill_values
end AspisR1.NCE_KeyCuts
