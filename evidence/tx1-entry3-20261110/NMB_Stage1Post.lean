import NMB_Stage1Result
import NMB_ReadonlyFrame
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Post
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 let out := G x ops p d (.ok ()) (.ok ()) (.ok ())
 out.post.snapshots.sdk=NMB_ReadonlyFrame.after x saved ∧
 out.post.snapshots.owned=[] ∧ out.post.checkpoint=none ∧
 out.post.snapshots.next=3 ∧ out.post.snapshots.input=x := by
 have child := (NLD_Stage1Source.erasure ops p (NMB_ThreeSnapshots.first x) d).trans branch
 have copied := NMB_Stage1CopyDomain.source x ops p d saved branch
 change (NLQ_CopyTrace.G (NMB_Stage1Tail.ready x).snapshots.sdk 2
   (NMB_Stage1Tail.ready x).snapshots.next (S2W_ReturnedCheckpoint.nativeBytes saved)).outcome=_ at copied
 dsimp only
 rw [NMB_Stage1Tail.source]
 simp only [continuation,child,copyResult,copied]
 exact ⟨rfl,True.intro,True.intro,rfl,rfl⟩
#print source
#print axioms source
end NMB_Stage1Post
