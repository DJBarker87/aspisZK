import NMB_Stage1Tail
import NMB_Stage1CopyDomain
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Result
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
/-- Copy-domain clauses are derived from the computed child branch, not
introduced as root premises or unconstrained native replies. -/
theorem copied (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key)
 (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 (copyResult (NMB_Stage1Tail.ready x) saved).result=.ok (.Ok ()) := by
 have h := NMB_Stage1CopyDomain.source x ops p d saved branch
 change (NLQ_CopyTrace.G (NMB_Stage1Tail.ready x).snapshots.sdk 2
   (NMB_Stage1Tail.ready x).snapshots.next (S2W_ReturnedCheckpoint.nativeBytes saved)).outcome=_ at h
 simp only [copyResult,h]
/-- Every child arm is split internally at its actual call expression. -/
theorem continuation (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) :
 (NMB_Stage1Source.continuation ops p d (NMB_ThreeSnapshots.first x) (NMB_Stage1Tail.ready x)).result=
 (do let child ← AdapterRw.r1_pool_adapter.owned.stage1_owned ops p (NMB_ThreeSnapshots.first x) d
     match child with
     | .Ok _ => ok (.Ok ())
     | .Err error => ok (.Err error)) := by
 have source := NLD_Stage1Source.erasure ops p (NMB_ThreeSnapshots.first x) d
 cases h : (NLD_Stage1Source.stage1Owned ops p (NMB_ThreeSnapshots.first x) d).2 with
 | fail error =>
   rw [←source,h]
   simp only [NMB_Stage1Source.continuation,h,bind_tc_fail]
 | div =>
   rw [←source,h]
   simp only [NMB_Stage1Source.continuation,h,bind_tc_div]
 | ok reply =>
   cases reply with
   | Err error =>
     rw [←source,h]
     simp only [NMB_Stage1Source.continuation,h,bind_tc_ok]
   | Ok saved =>
     have branch := source.symm.trans h
     rw [←source,h]
     simp only [NMB_Stage1Source.continuation,h,bind_tc_ok]
     exact copied x ops p d saved branch
theorem result (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) :
 (G x ops p d (.ok ()) (.ok ()) (.ok ())).result=
 (do let child ← AdapterRw.r1_pool_adapter.owned.stage1_owned ops p (NMB_ThreeSnapshots.first x) d
     match child with
     | .Ok _ => ok (.Ok ())
     | .Err error => ok (.Err error)) := by
 rw [NMB_Stage1Tail.source]
 exact continuation x ops p d
#print continuation
#print result
#print axioms copied
#print axioms continuation
#print axioms result
end NMB_Stage1Result
