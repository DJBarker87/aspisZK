import NLD_SourceSteps
import NIV_RawBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLD_Dispatch
open Aeneas Aeneas.Std Result AspisR1.NLD
abbrev Boundaries := NIV_RawBoundary.Boundaries
abbrev Key := Hiq_DispatchSource.Key
abbrev PR := core.result.Result Unit Hiq_DispatchSource.PE
/-- Every source branch invokes its child on the SAME original triple.
This is source syntax, not a native cut or a discharge of a child law. -/
def fallback {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) : Program PR :=
  .step .instructionTen (fun s => (ops.eq d (Array.make 2#usize [3#u8,10#u8]),s)) fun ten _ =>
  if ten then returned .dispatch (ops.first p a d)
  else .step .instructionEleven (fun s => (ops.eq d (Array.make 2#usize [3#u8,11#u8]),s)) fun eleven _ =>
    if eleven then returned .dispatch (ops.first p a d)
    else returned .dispatch (ops.second p a d)

def dispatch {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (value : Option U8) : Program PR :=
  match value with
  | none => fallback ops p a d
  | some i => match i with
    | 4#uscalar => returned .dispatch (ops.init p a d)
    | 5#uscalar => returned .dispatch (ops.write p a d)
    | 6#uscalar => returned .dispatch (ops.finalize p a d)
    | _ => fallback ops p a d

def process {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) : Program PR :=
  .step .head (fun s => (ops.head d,s)) fun h _ =>
  .step .copied (fun s => (ops.copy h,s)) fun value _ =>
    dispatch ops p a d value

def entry {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) : Program PR :=
  .step .admission (fun s => (ops.admitted d,s)) fun admitted _ =>
    if admitted then process ops p a d
    else .done (.Err .InvalidInstructionData)

theorem fallback_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (s : ParentState) :
    (run (fallback ops p a d) s).1 = (do
      let ten ← ops.eq d (Array.make 2#usize [3#u8,10#u8])
      if ten then ops.first p a d else do
        let eleven ← ops.eq d (Array.make 2#usize [3#u8,11#u8])
        if eleven then ops.first p a d else ops.second p a d) := by
  simp only [fallback,step_result,apply_ite,returned_result]

theorem dispatch_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (value : Option U8) (s : ParentState) :
    (run (dispatch ops p a d value) s).1 = match value with
    | none => (run (fallback ops p a d) s).1
    | some i => match i with
      | 4#uscalar => ops.init p a d
      | 5#uscalar => ops.write p a d
      | 6#uscalar => ops.finalize p a d
      | _ => (run (fallback ops p a d) s).1 := by
  cases value with
  | none => rfl
  | some i =>
    dsimp only [dispatch]
    split <;> simp only [returned_result]

theorem process_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (s : ParentState) :
    (run (process ops p a d) s).1 = NIV_RawBoundary.process ops p a d := by
  simp only [process,NIV_RawBoundary.process,step_result,dispatch_erasure,fallback_erasure]
  rfl

theorem entry_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (s : ParentState) :
    (run (entry ops p a d) s).1 = NIV_RawBoundary.entry ops p a d := by
  unfold entry NIV_RawBoundary.entry
  rw [step_result]
  congr 1
  funext admitted
  cases admitted <;> simp only [Bool.false_eq_true,ite_false,ite_true,run,process_erasure]

#print axioms fallback_erasure
#print axioms dispatch_erasure
#print axioms process_erasure
#print axioms entry_erasure
end AspisR1.NLD_Dispatch
