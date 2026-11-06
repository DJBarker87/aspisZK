import NLQ_Route
set_option autoImplicit false
noncomputable section
namespace NLQ_SourceDispatch
open Aeneas Aeneas.Std Result AspisR1
/-- Both TX1 instructions exclude every lifecycle and stage2 branch for ANY
callee installation. Unlike the earlier helper this does not install panic
stand-ins for branches that the caller must prove unreachable. -/
theorem process {A : Type} (children : Hiq_DispatchSource.Ops A)
 (p : Hiq_DispatchSource.Key) (a : Slice A) (d : Slice U8) (tx1 : NLQ_Route.Tx1 d) :
 NIV_RawBoundary.process (NIV_RawBoundary.profile children) p a d = children.first p a d := by
 rcases tx1 with h | h
 · have eq : d=NJD_Prefixes.ten := Subtype.ext h
   subst d
   simp [NIV_RawBoundary.process,NIV_RawBoundary.profile,Hiq_DispatchSource.firstByte,
    Hiq_DispatchSource.copied,Hiq_DispatchSource.eqU8,NJD_Prefixes.ten,Array.make]
   rfl
 · have eq : d=NJD_Prefixes.eleven := Subtype.ext h
   subst d
   simp [NIV_RawBoundary.process,NIV_RawBoundary.profile,Hiq_DispatchSource.firstByte,
    Hiq_DispatchSource.copied,Hiq_DispatchSource.eqU8,NJD_Prefixes.eleven,Array.make]
   rfl
/-- Entry retains rejected admission and outer abort prefixes verbatim; the
actual source admission function is supplied by profile, not a free Bool. -/
theorem entry {A : Type} (children : Hiq_DispatchSource.Ops A)
 (p : Hiq_DispatchSource.Key) (a : Slice A) (d : Slice U8) :
 NIV_RawBoundary.entry (NIV_RawBoundary.profile children) p a d =
 (do let admitted ← (NIV_RawBoundary.profile children).admitted d
     if admitted then NIV_RawBoundary.process (NIV_RawBoundary.profile children) p a d
     else ok (.Err .InvalidInstructionData)) := rfl
#check @process
#check @entry
#print axioms process
#print axioms entry
end NLQ_SourceDispatch
