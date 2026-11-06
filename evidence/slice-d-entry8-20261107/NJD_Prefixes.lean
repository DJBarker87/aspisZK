import NJD_EntrySpine
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJD_Prefixes
open Aeneas Aeneas.Std Result NJD_Trace NJD_EntrySpine

/-- The entry's admission call is retained on an abort, and no child exists. -/
theorem admission_fail {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8) (e : Error)
    (reply : ops.admitted d = .fail e) :
    entry ops p a d = ([.admission d],.fail e) := by
  simp only [entry,reply,call,NJD_Trace.bind]

theorem admission_div {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8)
    (reply : ops.admitted d = .div) :
    entry ops p a d = ([.admission d],.div) := by
  simp only [entry,reply,call,NJD_Trace.bind]

theorem rejected {Account : Type} (ops : Boundaries Account)
    (p : Key) (a : Slice Account) (d : Slice U8)
    (reply : ops.admitted d = .ok false) :
    entry ops p a d = ([.admission d],.ok (.Err .InvalidInstructionData)) := by
  simp only [entry,reply,call,NJD_Trace.bind,Bool.false_eq_true,ite_false,NJD_Trace.pure,List.append_nil]

def ten : Slice U8 := ⟨[3#u8,10#u8],by scalar_tac⟩
def eleven : Slice U8 := ⟨[3#u8,11#u8],by scalar_tac⟩

theorem first_ten {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Key) (a : Slice Account) :
    entry (NIV_RawBoundary.profile ops) p a ten =
      ([.admission ten,.head ten,.copied (some (3#u8)),
        .equal ten (Array.make 2#usize [3#u8,10#u8]),.child 1 p a ten],
       ops.first p a ten) := by
  simp [entry,process,dispatch,fallback,child,NIV_RawBoundary.profile,
    Hiq_DispatchSource.pool_route.admitted,Hiq_DispatchSource.eqU8,
    Hiq_DispatchSource.firstByte,Hiq_DispatchSource.copied,
    NJD_Trace.bind,call,ten,Array.make]
  constructor <;> rfl

theorem first_eleven {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Key) (a : Slice Account) :
    entry (NIV_RawBoundary.profile ops) p a eleven =
      ([.admission eleven,.head eleven,.copied (some (3#u8)),
        .equal eleven (Array.make 2#usize [3#u8,10#u8]),
        .equal eleven (Array.make 2#usize [3#u8,11#u8]),.child 1 p a eleven],
       ops.first p a eleven) := by
  simp [entry,process,dispatch,fallback,child,NIV_RawBoundary.profile,
    Hiq_DispatchSource.pool_route.admitted,Hiq_DispatchSource.eqU8,
    Hiq_DispatchSource.firstByte,Hiq_DispatchSource.copied,
    NJD_Trace.bind,call,eleven,Array.make]
  constructor <;> rfl

#print axioms admission_fail
#print axioms admission_div
#print axioms rejected
#print axioms first_ten
#print axioms first_eleven
end AspisR1.NJD_Prefixes
end
