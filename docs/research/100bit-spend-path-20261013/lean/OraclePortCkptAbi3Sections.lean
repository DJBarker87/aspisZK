import OraclePortCkptAbi2Unwrap

/-! Fixed part list and short-circuit composition. Atomic semantic joins
remain explicit hypotheses. This does not identify the emitted resume caller
or construct its heap/iterator implementation. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbi3Sections
open AspisR1Stage2 OraclePortCkptAbiReadSequence OraclePortCkptAbi2Unwrap

inductive Section where
  | stateRoots | challenges | rho | queries | semanticAlpha | coordinates
  | claimRhs | power | weights
  deriving DecidableEq

def schedule : List Section :=
  [.stateRoots,.challenges,.rho,.queries,.semanticAlpha,.coordinates,.claimRhs,.power,.weights]

def widths : Section → List Usize
  | .stateRoots => List.replicate 3 32#usize
  | .challenges => List.replicate 4 32#usize
  | .rho => [16#usize]
  | .queries => List.replicate 22 4#usize
  | .semanticAlpha => List.replicate 10 16#usize
  | .coordinates => List.replicate 4 16#usize
  | .claimRhs => List.replicate 2 32#usize
  | .power => [16#usize]
  | .weights => List.replicate 64 16#usize

theorem schedule_exact : schedule.flatMap widths = savedTenWidths := by
  simp only [schedule,List.flatMap_cons,List.flatMap_nil,widths,List.append_nil,
    savedTenWidths]
  rw [show (7 : Nat) = 3+4 from rfl, List.replicate_add,
    show (14 : Nat) = 10+4 from rfl, List.replicate_add]
  simp only [List.append_assoc]

/-- Full fixed raw layout, for every panic continuation; no full byte vector
is reduced in the proof. Field-decoder rejection is handled by run below. -/
theorem raw_schedule_total
    (panic : (n : Usize) → core.array.TryFromSliceError → Result (Array U8 n))
    (ck : Slice U8) (length : ck.val.length = 1768) :
    ∃ out, readMany (fun n => unwrapWithPanic (panic n)) ⟨ck,80#usize⟩
      (schedule.flatMap widths) =
      ok (blocks ck.val 80 (schedule.flatMap widths),out) ∧
      out.at.val = 1736 ∧ out.bytes = ck := by
  rw [schedule_exact]
  exact savedTen_reads_total _ (fun _ _ => rfl) ck length

/-- S includes every mutable output/cursor; E can include failure post-state.
Except retains the exact ordinary error and never executes the suffix after
failure. Neither success nor accepted input is assumed. -/
def run {S E : Type} (step : Section → S → Except E S) :
    List Section → S → Except E S
  | [], s => .ok s
  | part::rest, s => (step part s).bind (run step rest)

theorem run_eq {S E : Type} (source model : Section → S → Except E S)
    (sections : List Section)
    (atomic : ∀ part, part ∈ sections → ∀ s, source part s = model part s)
    (s : S) : run source sections s = run model sections s := by
  induction sections generalizing s with
  | nil => rfl
  | cons part rest ih =>
    simp only [run]
    rw [atomic part (by simp) s]
    cases h : model part s with
    | error e => rfl
    | ok out =>
      exact ih (fun a ha t => atomic a (List.mem_cons_of_mem part ha) t) out

theorem fixed_composition {S E : Type} (source model : Section → S → Except E S)
    (atomic : ∀ part, part ∈ schedule → ∀ s, source part s = model part s)
    (s : S) : run source schedule s = run model schedule s :=
  run_eq source model schedule atomic s

#print axioms schedule_exact
#print axioms raw_schedule_total
#print axioms run_eq
#print axioms fixed_composition
end AspisR1.OraclePortCkptAbi3Sections
