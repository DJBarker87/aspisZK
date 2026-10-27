import R1Z.PDict_OwnedPrefix262
set_option autoImplicit false
namespace R1Z.PDict_OwnedLoop262
open Aeneas Aeneas.Std Result ControlFlow PDict_OwnedPrefix262
abbrev Variant := PDict_OwnedCell262.Variant

/-- Each actual extracted row call selects the corresponding desired element.
This is an explicit local premise until concrete row correctness is installed. -/
def RowReads {T : Type} (variant : Variant) (rows target : Array T 1024#usize) : Prop :=
  ∀ (index : Usize) (small : index.val < 1024),
    ∃ (source : Usize) (sourceBound : source.val < rows.length),
      PDict_OwnedSource244.row.row variant index = .ok source ∧
      rows[source] = coordinate target index small

def Coordinates {T : Type} (out target : Array T 1024#usize) : Prop :=
  ∀ (index : Usize) (bound : index.val < 1024),
    coordinate out index bound = coordinate target index bound

/-- All element types and arrays; one-step symbolic unfolding with decreasing
remaining count. The row-read premise is not native coefficient adequacy. -/
theorem loop_coordinates {T : Type} (variant : Variant) (rows target out : Array T 1024#usize)
    (index : Usize) (reads : RowReads variant rows target) (prior : Prefix out target index) :
    ∃ result, PDict_OwnedSource244.coefficients.owned_loop variant rows out index = .ok result ∧
      Coordinates result target := by
  let body := fun state : (Array T 1024#usize) × Usize =>
    PDict_OwnedSource244.coefficients.owned_loop.body variant rows state.1 state.2
  have main : ∀ n (i : Usize) (current : Array T 1024#usize), 1024-i.val=n →
      Prefix current target i →
      ∃ result, Aeneas.Std.loop body (current,i) = .ok result ∧ Coordinates result target := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i current remaining correctPrefix
      by_cases small : i.val < 1024
      · obtain ⟨source, sourceBound, rowCall, valueCorrect⟩ := reads i small
        have nextPrefix := PDict_OwnedPrefix262.extend current target i small
          rows[source] valueCorrect correctPrefix
        have decreased : 1024-(Usize.wrapping_add i 1#usize).val < n := by
          rw [PDict_Advance244.value i small]
          omega
        obtain ⟨result, run, good⟩ := ih _ decreased _ _ rfl nextPrefix
        refine ⟨result, ?_, good⟩
        rw [Aeneas.Std.loop.eq_def]
        dsimp only [body]
        rw [PDict_OwnedCell262.cell variant rows current i source small sourceBound rowCall]
        exact run
      · have large : 1024 ≤ i.val := by omega
        refine ⟨current, ?_, ?_⟩
        · rw [Aeneas.Std.loop.eq_def]
          dsimp only [body]
          rw [PDict_OwnedCell262.done_cell variant rows current i large]
        · intro k bound
          exact correctPrefix k bound (by omega)
  have run := main (1024-index.val) index out rfl prior
  simpa only [PDict_OwnedSource244.coefficients.owned_loop, Aeneas.Std.uncurry, body] using run

#print axioms RowReads
#print axioms Coordinates
#print axioms loop_coordinates
end R1Z.PDict_OwnedLoop262
