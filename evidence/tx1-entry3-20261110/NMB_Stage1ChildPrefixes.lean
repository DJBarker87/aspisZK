import NMB_Stage1Tail
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1ChildPrefixes
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
/-- Error is an actual branch expression, never a root hypothesis. Owned
cleanup follows returned Err, whereas fail/div have no cleanup suffix. -/
theorem fail (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (err : Aeneas.Std.Error)
 (branch : (NLD_Stage1Source.stage1Owned ops p (NMB_ThreeSnapshots.first x) d).2=.fail err) :
 let s := NMB_Stage1Tail.ready x
 G x ops p d (.ok ()) (.ok ()) (.ok ())=
 ⟨.fail err,s,(NMB_ThreeSnapshots.G x (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  [.owned s s p (NMB_ThreeSnapshots.first x) d (.fail err)
    (NLD_Stage1Source.stage1Owned ops p (NMB_ThreeSnapshots.first x) d).1]⟩ := by
 dsimp only
 rw [NMB_Stage1Tail.source]
 simp only [continuation,branch]
theorem divergence (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (branch : (NLD_Stage1Source.stage1Owned ops p (NMB_ThreeSnapshots.first x) d).2=.div) :
 let s := NMB_Stage1Tail.ready x
 G x ops p d (.ok ()) (.ok ()) (.ok ())=
 ⟨.div,s,(NMB_ThreeSnapshots.G x (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  [.owned s s p (NMB_ThreeSnapshots.first x) d .div
    (NLD_Stage1Source.stage1Owned ops p (NMB_ThreeSnapshots.first x) d).1]⟩ := by
 dsimp only
 rw [NMB_Stage1Tail.source]
 simp only [continuation,branch]
#print fail
#print divergence
#print axioms fail
#print axioms divergence
end NMB_Stage1ChildPrefixes
