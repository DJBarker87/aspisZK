import NMB_Stage1Post
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Readonly
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 let sdk := (G x ops p d (.ok ()) (.ok ()) (.ok ())).post.snapshots.sdk
 sdk.cells (x.sdk.accounts 0).data=x.sdk.cells (x.sdk.accounts 0).data ∧
 sdk.cells (x.sdk.accounts 1).data=x.sdk.cells (x.sdk.accounts 1).data := by
 dsimp only
 rw [(NMB_Stage1Post.source x ops p d saved branch).1]
 exact NMB_ReadonlyFrame.source x ops p d saved branch
#print source
#print axioms source
end NMB_Stage1Readonly
