import Aeneas

open Aeneas Aeneas.Std

namespace PV_UC_FormattingObstruction

-- Diagnostic only: this records information lost by the existing model.
-- It is neither a formatter source law nor a privacy-premise discharge.
def fdArguments {T : Type} (display : core.fmt.Display T) (fd : T) :
    Result core.fmt.Arguments := do
  let a ← core.fmt.rt.Argument.new_display display fd
  core.fmt.Arguments.new
    (Array.make 17#usize [14#u8, 47#u8, 112#u8, 114#u8, 111#u8, 99#u8,
      47#u8, 115#u8, 101#u8, 108#u8, 102#u8, 47#u8, 102#u8, 100#u8,
      47#u8, 192#u8, 0#u8])
    (Array.make 1#usize [a])

theorem fdArguments_equal {T : Type} (display : core.fmt.Display T)
    (fd3 fd4 : T) : fdArguments display fd3 = fdArguments display fd4 := rfl

theorem no_faithful_fd_formatter {T : Type} (display : core.fmt.Display T)
    (fd3 fd4 : T) :
    ¬ ∃ format : core.fmt.Arguments → Result String,
      (fdArguments display fd3 >>= format) = .ok "/proc/self/fd/3" ∧
      (fdArguments display fd4 >>= format) = .ok "/proc/self/fd/4" := by
  rintro ⟨format, h3, h4⟩
  have collapse := congrArg (fun a => a >>= format)
    (fdArguments_equal display fd3 fd4)
  have h : (Result.ok "/proc/self/fd/3" : Result String) =
      .ok "/proc/self/fd/4" := h3.symm.trans (collapse.trans h4)
  have bad : ("/proc/self/fd/3" : String) = "/proc/self/fd/4" := by
    injection h
  exact (by decide : ("/proc/self/fd/3" : String) ≠ "/proc/self/fd/4") bad

#print axioms fdArguments_equal
#print axioms no_faithful_fd_formatter

end PV_UC_FormattingObstruction
