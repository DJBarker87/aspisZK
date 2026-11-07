import NMB_DataAccess
import NMB_CheckpointExtent
set_option autoImplicit false
noncomputable section
namespace NMB_AcceptedExtents
open Aeneas Aeneas.Std Result AspisR1
/-- All three extents follow from the SAME child call and its OWN snapshot
reads. No key-comparison law, selected-success root or coalesced flag premise. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 (x.buffers (x.handles 0).1).val.length=58295 ∧
 (x.buffers (x.handles 1).1).val.length=1880 ∧
 (x.buffers (x.handles 2).1).val.length=1768 := by
 obtain ⟨pa,pu,pub,proof,statement,semantic,selected,split,start,finish,
  ip,iu,rp,ru,_⟩ := AdapterRw.Cuts.stage1_call ops p (NMB_ThreeSnapshots.first x) d saved accepted
 have eqp := Result.ok.inj (ip.symm.trans (NMB_FirstIndex.source x).1)
 have equ := Result.ok.inj (iu.symm.trans (NMB_FirstIndex.source x).2.1)
 subst pa
 subst pu
 exact ⟨(NMB_DataAccess.fixed x ops 0 58295 proof rp).2,
  (NMB_DataAccess.fixed x ops 1 1880 pub ru).2,
  NMB_CheckpointExtent.source x ops p d saved accepted⟩
#print source
#print axioms source
end NMB_AcceptedExtents
