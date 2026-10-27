import RPz7_FIp_NativeDots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_DotsAdapter
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
abbrev NE := FIo_Install.NE

def toArray {N : Usize} (a : Array E N) : Array NE N :=
  ⟨a.val.map FIo_Install.toE,by simpa only [List.length_map] using a.property⟩
def fromArray {N : Usize} (a : Array NE N) : Array E N :=
  ⟨a.val.map FIo_Install.fromE,by simpa only [List.length_map] using a.property⟩

def dots (q : Slice U8) (g : Array E 29#usize) : Result (Array E 4#usize) := do
  let out ← FIp_NativeDots.fast_dots.four_dots q (toArray g)
  ok (fromArray out)

theorem reached (q : Slice U8) (g : Array E 29#usize) (out : Array E 4#usize)
    (run : dots q g=ok out) :
    ∃ nativeOut,FIp_NativeDots.fast_dots.four_dots q (toArray g)=ok nativeOut ∧ fromArray nativeOut=out := by
  obtain ⟨nativeOut,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨nativeOut,hn,Result.ok.inj run⟩

#print axioms reached
end AspisR1.FIp_DotsAdapter
end
