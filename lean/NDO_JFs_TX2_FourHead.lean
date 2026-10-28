import RPt_JFr_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_FourHead
open Aeneas Aeneas.Std Result
abbrev NE := FIo_Install.NE

/-- The actual four native slot calls after the computed physical prefix. -/
def slots (q : Array U8 608#usize) (g : Array NE 29#usize) : Result (Array NE 4#usize) := do
  let a ← FIp_NativeDots.fast_dots.four_dots_one q g 0#usize
  let b ← FIp_NativeDots.fast_dots.four_dots_one q g 1#usize
  let c ← FIp_NativeDots.fast_dots.four_dots_one q g 2#usize
  let d ← FIp_NativeDots.fast_dots.four_dots_one q g 3#usize
  ok (Array.make 4#usize [a,b,c,d])

theorem source (i : Fin 22) (g : Array NE 29#usize) :
    FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value i) g=
      slots (JFr_TX2_Windows.array i) g := by
  have joined := congrArg (fun selected : Result (Array U8 608#usize) => do
    let q ← selected
    slots q g) (JFr_TX2_Windows.read i)
  simpa only [FIp_NativeDots.fast_dots.four_dots,slots,bind_assoc_eq,bind_tc_ok] using joined

#print axioms source
end AspisR1.JFs_TX2_FourHead
end
