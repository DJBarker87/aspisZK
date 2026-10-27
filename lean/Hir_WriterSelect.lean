import Hir_RecordNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_WriterSelect
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel

structure Writer (A : Type) where
  site : CallAt A
  saved : alloc.vec.Vec U8
  post : Heap (Nat → Record)
  final : A

/-- Pure deterministic scan over REACHED observations. No oracle H, chosen
log, existential source cut or provenance law is an input to selection. -/
def one {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (key : Nat) (data : Slice U8)
    (site : CallAt A) : Option (Writer A) := by
  classical
  exact if Hiq_ReleaseRoute.route site.call.data = .first ∧ (site.call.layout.handles 2).1 = key then
    match first native1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state with
    | .ok (.Ok (saved,post,final)) =>
      if data = saved.deref then some ⟨site,saved,post,final⟩ else none
    | _ => none
  else none

def search {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (key : Nat) (data : Slice U8) :
    List (CallAt A) → Option (Writer A)
  | [] => none
  | site :: rest => match one native1 copy allocator id key data site with
    | some writer => some writer
    | none => search native1 copy allocator id key data rest

end AspisR1.Hir_WriterSelect
end
