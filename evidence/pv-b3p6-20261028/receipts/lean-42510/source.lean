import PV_B3P_Install133
namespace PV_B3P_Result133
open Aeneas Aeneas.Std Result
set_option autoImplicit false

-- Generic error carrier; the transport never silently turns failure into success.
def translate (E : Type) (r : Result (Array U16 214#usize)) :
    Result (core.result.Result (alloc.vec.Vec U16) E) := do
  let rows ← r
  ok (.Ok (PV_B3P_Install133.toVec rows))

theorem fail_tag (E : Type) (e : Aeneas.Std.Error) :
    translate E (.fail e) = .fail e := rfl

theorem div_tag (E : Type) : translate E .div = .div := rfl

theorem ok_tag (E : Type) (rows : Array U16 214#usize) :
    translate E (.ok rows) = .ok (.Ok (PV_B3P_Install133.toVec rows)) := rfl

theorem source (E : Type) :
    translate E PV_B3P_133.reference133.active_rows =
      .ok (.Ok PV_B3P_Install133.value) := by
  rw [PV_B3P_Law133.source]
  rfl

#print axioms fail_tag
#print axioms div_tag
#print axioms ok_tag
#print axioms source
end PV_B3P_Result133
