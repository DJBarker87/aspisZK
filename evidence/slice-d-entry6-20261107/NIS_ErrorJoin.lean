import NIS_ArgumentMetadata
set_option autoImplicit false
noncomputable section
namespace NIJ_ErrorJoin
open Aeneas Aeneas.Std Result
abbrev E := NGL_ErrorModel.E
abbrev PE := NGL_ErrorModel.PE

/-- The native Arguments metadata packet selects the real writer path.
The finite native writer packets realize these exact ordered fragments. -/
def formatted (e : E) : String :=
 Option.elim (NIJ_ArgumentMetadata.image e).2
  (String.join (NHY_ErrorFragments.fragments e)) id

theorem bytes (e : E) : formatted e=NGL_ErrorModel.message e := by
 exact NHY_ErrorFragments.ordered_message e

/-- Source control shape: one logging action, then InvalidInstructionData.
The action retains its full Result, including allocator/runtime abort prefixes.
Its returning realization is the exact native format/syscall/cleanup packet;
there is no assumed successful logging action. -/
def run {S : Type} (emit : String → S → Result S) (e : E) (s : S) : Result (PE × S) := do
 let after ← emit (formatted e) s
 ok (.InvalidInstructionData,after)

theorem source {S : Type} (emit : String → S → Result S) (e : E) (s : S) :
 run emit e s=NGL_ErrorModel.run emit e s := by
 unfold run NGL_ErrorModel.run
 rw [bytes]

/-- Every returning source case is covered by the certified eight-label table. -/
theorem exhaustive (e : E) : (e,formatted e) ∈ NHD_ErrorLabels.casesTable := by
 rw [bytes]
 exact NHD_ErrorLabels.exhaustive e

/-- No source suffix is invented when the logging/allocator action aborts. -/
theorem abort_prefix {S : Type} (emit : String → S → Result S) (e : E) (s : S) :
 run emit e s=match emit (formatted e) s with
 | .ok after => .ok (.InvalidInstructionData,after)
 | .fail err => .fail err
 | .div => .div := by
 cases h : emit (formatted e) s <;> simp only [run,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

#print axioms bytes
#print axioms source
#print axioms exhaustive
#print axioms abort_prefix
end NIJ_ErrorJoin
