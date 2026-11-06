import NJD_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJD_EntrySpine
open Aeneas Aeneas.Std Result
open NJD_Trace
abbrev Boundaries := NIV_RawBoundary.Boundaries
abbrev Key := Hiq_DispatchSource.Key
abbrev PE := Hiq_DispatchSource.PE
abbrev PR := core.result.Result Unit PE

inductive Event (Account : Type) where
  | admission (data : Slice U8)
  | head (data : Slice U8)
  | copied (value : Option U8)
  | equal (data : Slice U8) (bytes : Array U8 2#usize)
  | child (kind : Nat) (program : Key) (accounts : Slice Account) (data : Slice U8)

def child {Account : Type} (kind : Nat) (p : Key) (a : Slice Account) (d : Slice U8)
    (reply : Result PR) : Run (Event Account) PR := call (.child kind p a d) reply

def fallback {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) : Run (Event Account) PR :=
  NJD_Trace.bind (call (.equal d (Array.make 2#usize [3#u8,10#u8]))
    (ops.eq d (Array.make 2#usize [3#u8,10#u8]))) fun ten =>
  if ten then child 1 p a d (ops.first p a d)
  else NJD_Trace.bind (call (.equal d (Array.make 2#usize [3#u8,11#u8]))
    (ops.eq d (Array.make 2#usize [3#u8,11#u8]))) fun eleven =>
    if eleven then child 1 p a d (ops.first p a d)
    else child 2 p a d (ops.second p a d)

def dispatch {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (value : Option U8) : Run (Event Account) PR :=
  match value with
  | none => fallback ops p a d
  | some i => match i with
    | 4#uscalar => child 4 p a d (ops.init p a d)
    | 5#uscalar => child 5 p a d (ops.write p a d)
    | 6#uscalar => child 6 p a d (ops.finalize p a d)
    | _ => fallback ops p a d

def process {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) : Run (Event Account) PR :=
  NJD_Trace.bind (call (.head d) (ops.head d)) fun h =>
  NJD_Trace.bind (call (.copied h) (ops.copy h)) fun value =>
    dispatch ops p a d value

def entry {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) : Run (Event Account) PR :=
  NJD_Trace.bind (call (.admission d) (ops.admitted d)) fun admitted =>
    if admitted then process ops p a d else
      NJD_Trace.pure (.Err .InvalidInstructionData)

theorem fallback_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) :
    (fallback ops p a d).2 = (do
      let ten ← ops.eq d (Array.make 2#usize [3#u8,10#u8])
      if ten then ops.first p a d else do
        let eleven ← ops.eq d (Array.make 2#usize [3#u8,11#u8])
        if eleven then ops.first p a d else ops.second p a d) := by
  simp only [fallback,erase_bind,call,child,apply_ite]

theorem dispatch_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (value : Option U8) :
    (dispatch ops p a d value).2 = match value with
    | none => (fallback ops p a d).2
    | some i => match i with
      | 4#uscalar => ops.init p a d
      | 5#uscalar => ops.write p a d
      | 6#uscalar => ops.finalize p a d
      | _ => (fallback ops p a d).2 := by
  cases value with
  | none => rfl
  | some i =>
    dsimp only [dispatch]
    split <;> rfl

/-- Model erasure; every entered child retains its complete Result. -/
theorem process_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) :
    (process ops p a d).2 = NIV_RawBoundary.process ops p a d := by
  simp only [process,NIV_RawBoundary.process,erase_bind,call,dispatch_erasure,fallback_erasure]
  rfl

theorem entry_erasure {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) :
    (entry ops p a d).2 = NIV_RawBoundary.entry ops p a d := by
  unfold entry NIV_RawBoundary.entry
  rw [erase_bind]
  simp only [call]
  congr 1
  funext admitted
  cases admitted <;> simp only [Bool.false_eq_true,ite_false,ite_true,NJD_Trace.pure,process_erasure]

/-- The concrete primitive profile consumes the predecessor's actual emission. -/
theorem emitted {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Key) (a : Slice Account) (d : Slice U8) :
    (entry (NIV_RawBoundary.profile ops) p a d).2 = NIV_ExtractedForward.entry ops p a d := by
  rw [entry_erasure,NIV_RawBoundary.entry_profile]

#print axioms fallback_erasure
#print axioms dispatch_erasure
#print axioms process_erasure
#print axioms entry_erasure
#print axioms emitted
end AspisR1.NJD_EntrySpine
end
