import NJD_Prefixes
import NLD_DispatchFold
set_option autoImplicit false
noncomputable section
namespace NLQ_Route
open Aeneas Aeneas.Std Result AspisR1
abbrev Key := Hiq_DispatchSource.Key
abbrev Reply := core.result.Result Unit Hiq_DispatchSource.PE
/-- TX1's admitted instruction domain includes 11, although stage1_owned
subsequently rejects it. No successful-child condition is used. -/
def Tx1 (d : Slice U8) : Prop :=
 d.val = [3#u8,10#u8] ∨ d.val = [3#u8,11#u8]
/-- Only an intermediate child parameter under (bd). Non-TX1 branches stay
present in the emitted process; this dictionary is internal, not a root input. -/
def children {A : Type} (first : Key → Slice A → Slice U8 → Result Reply) : Hiq_DispatchSource.Ops A :=
 ⟨first,fun _ _ _ => .fail .panic,fun _ _ _ => .fail .panic,
  fun _ _ _ => .fail .panic,fun _ _ _ => .fail .panic⟩
theorem process_ten {A : Type} (first : Key → Slice A → Slice U8 → Result Reply)
 (p : Key) (a : Slice A) :
 NIV_RawBoundary.process (NIV_RawBoundary.profile (children first)) p a NJD_Prefixes.ten =
 first p a NJD_Prefixes.ten := by
 simp [NIV_RawBoundary.process,NIV_RawBoundary.profile,Hiq_DispatchSource.firstByte,
  Hiq_DispatchSource.copied,Hiq_DispatchSource.eqU8,NJD_Prefixes.ten,children,Array.make]
 rfl
theorem process_eleven {A : Type} (first : Key → Slice A → Slice U8 → Result Reply)
 (p : Key) (a : Slice A) :
 NIV_RawBoundary.process (NIV_RawBoundary.profile (children first)) p a NJD_Prefixes.eleven =
 first p a NJD_Prefixes.eleven := by
 simp [NIV_RawBoundary.process,NIV_RawBoundary.profile,Hiq_DispatchSource.firstByte,
  Hiq_DispatchSource.copied,Hiq_DispatchSource.eqU8,NJD_Prefixes.eleven,children,Array.make]
 rfl
/-- Exact complete Result: lifecycle/stage2 are unreachable on TX1 input.
This is a source theorem; a native parent window is a separate obligation. -/
theorem process {A : Type} (first : Key → Slice A → Slice U8 → Result Reply)
 (p : Key) (a : Slice A) (d : Slice U8) (domain : Tx1 d) :
 NIV_RawBoundary.process (NIV_RawBoundary.profile (children first)) p a d = first p a d := by
 rcases domain with h | h
 · have eq : d = NJD_Prefixes.ten := Subtype.ext h
   subst d; exact process_ten first p a
 · have eq : d = NJD_Prefixes.eleven := Subtype.ext h
   subst d; exact process_eleven first p a
#print axioms process_ten
#print axioms process_eleven
#print axioms process
#print process
end NLQ_Route
