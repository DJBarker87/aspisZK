import S8JoinAccumulatorStage

/-! Construction-owned realization of the frozen field accumulator. This is
a canonical MODEL state, not a claimed identity with reached Rust storage.
S7 must still identify its source state with these field values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinModelRepresentation
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
attribute [local instance] Classical.propDecidable
open S8OwnedP6ValueModel S8OwnedP6Finish S8JoinFinishField S8JoinAccumulatorStage

/-- Logical field coordinates in the same order as the source's raw lanes. -/
def limb (q : QM31Exact) (k : Fin 4) : M31Exact :=
  match k.val with | 0 => q.re.re | 1 => q.re.im | 2 => q.im.re | _ => q.im.im

def rawLimb (a : M31Exact) : U64 := UScalar.ofNatCore a.val (by
  have h := ZMod.val_lt a
  change a.val < 2147483647 at h
  change a.val < 18446744073709551616
  omega)

def row (q : QM31Exact) : Row :=
  Array.make 4#usize [rawLimb q.re.re,rawLimb q.re.im,rawLimb q.im.re,rawLimb q.im.im]

theorem row_limb (q : QM31Exact) (k : Fin 4) :
    (rowAt (row q) k).val = (limb q k).val := by
  fin_cases k <;> simp [rowAt,row,limb,Array.make,rawLimb]

theorem row_field (q : QM31Exact) : rawValue (row q)=q := by
  cases q with
  | mk a b =>
    cases a with
    | mk a0 a1 =>
      cases b with
      | mk b0 b1 => simp [rawValue,row,rowAt,Array.make,rawLimb]

def raw (w : Fin 64 → QM31Exact) : Raw :=
  ⟨List.ofFn (fun l => row (w l)),by simp only [List.length_ofFn]; scalar_tac⟩

def old : Weights :=
  ⟨List.replicate 64 (⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ : Q),by
    simp only [List.length_replicate]; scalar_tac⟩

theorem raw_row (w : Fin 64 → QM31Exact) (l : Fin 64) (r : Row)
    (read : (raw w).val[l.val]?=some r) : r=row (w l) := by
  have h : (raw w).val[l.val]?=some (row (w l)) := by
    change (List.ofFn fun i => row (w i))[l.val]?=some (row (w l))
    rw [List.getElem?_ofFn,dif_pos l.isLt]
  exact Option.some.inj (read.symm.trans h)

/-- The old natural-coordinate certificate conditions hold at this logical
state by construction, with neither phase bounds nor congruence premises. -/
theorem model_caller (w : Fin 64 → QM31Exact) :
    S8Kani2CallerJoin.CallerInvariant (raw w) old
      (fun j k => if h:j<64 then (limb (w ⟨j,h⟩) k).val else 0) := by
  refine ⟨by simp [raw,old],?_⟩
  intro j r read k
  have bound : j<64 := by
    by_contra h
    have no : (raw w).val[j]?=none := List.getElem?_eq_none (by simpa [raw] using Nat.le_of_not_gt h)
    rw [no] at read
    contradiction
  have same := raw_row w ⟨j,bound⟩ r read
  subst r
  rw [row_limb,dif_pos bound]

/-- Total logical reference S8 stage for every frozen q/rho and field data,
including an arithmetic false result. No successful dV premise is required. -/
theorem model_finish_check (data : Data) (q : Queries) (rho : QM31Exact) :
    ∃ out : Weights, S8OwnedP6.finish_owned (raw (weight q rho)) old=.ok out ∧
      check out data q rho =
        decide (HchecksAccumulator.ClosedSum LiteralOpeningView.eK data q rho) := by
  apply finish_check
  · simp [old]
  · simp [old,raw]
  · intro l r read
    rw [raw_row _ l r read,row_field]

def modelCheck (data : Data) (q : Queries) (rho : QM31Exact) : Bool :=
  check (S8JoinFinishExact.output (raw (weight q rho)) old) data q rho

theorem model_check_eq (data : Data) (q : Queries) (rho : QM31Exact) :
    modelCheck data q rho =
      decide (HchecksAccumulator.ClosedSum LiteralOpeningView.eK data q rho) := by
  obtain ⟨out,run,checked⟩ := model_finish_check data q rho
  have exactRun := S8JoinFinishExact.reference_exact (raw (weight q rho)) old
    (by simp [old,raw])
  have same := Result.ok.inj (run.symm.trans exactRun)
  simpa only [modelCheck,same] using checked

#print axioms row_limb
#print axioms row_field
#print axioms raw_row
#print axioms model_caller
#print axioms model_finish_check
#print axioms model_check_eq
end AspisR1.S8JoinModelRepresentation
end
