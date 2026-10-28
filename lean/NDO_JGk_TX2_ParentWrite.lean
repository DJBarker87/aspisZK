import NDO_JGk_TX2_NativeLeaves
import MultiproofConePhysicalAddress
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_ParentWrite
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def parentIndex (index : U32) : U32 := UScalar.ofNat (index.val/2) (by scalar_tac)
def next (w : Usize) (room : w.val<16) : Usize := UScalar.ofNat (w.val+1) (by scalar_tac)
def after (s : reference.Scratch) (index : U32) (w : Usize) (value : Array U8 32#usize)
    (cursor : Usize) : reference.Scratch :=
  {s with idx:=s.idx.set w (parentIndex index),val:=s.val.set w value,«at»:=cursor}

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (left right out : State) (ni cursor : Usize) (index : U32) (w : Usize)
    (room : w.val<16)
    (hashed : JFp_SHADigest.digest (BinMerkle32Path.nodeInput (OracleDecisionMultiTree.children left right))=out) :
    reference.write_parent (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s (encodeState left) (encodeState right) ni cursor index w=
      ok (.Next (after s index w (encodeState out) cursor) ni (next w room)) := by
  let D' := Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)
  have total : MultiproofConeNodeDomain.HashTotal D' hash := by
    intro input
    exact ⟨encodeState (JFp_SHADigest.digest (flatten input)),rfl⟩
  have call : D'.digest hash (MultiproofConePhysicalDigest.parts (encodeState left) (encodeState right))=
      ok (encodeState out) := by
    change ok (encodeState (JFp_SHADigest.digest (flatten
      (MultiproofConePhysicalDigest.parts (encodeState left) (encodeState right)))))=_
    rw [MultiproofConePhysicalAddress.parent_address,state_roundtrip,state_roundtrip,hashed]
  obtain ⟨returned,run,post⟩ := WP.spec_imp_exists
    (MultiproofConePhysicalDigest.write_observed D' hash total s (encodeState left) (encodeState right)
      ni cursor index w room)
  obtain ⟨value,parent,nw,observed,parentVal,nextVal,state⟩ := post
  have valueEq : value=encodeState out := Result.ok.inj (observed.symm.trans call)
  have parentEq : parent=parentIndex index := UScalar.eq_of_val_eq parentVal
  have nextEq : nw=next w room := UScalar.eq_of_val_eq nextVal
  rw [valueEq,parentEq,nextEq] at state
  exact run.trans (congrArg ok state)
#print axioms source
end AspisR1.JGk_TX2_ParentWrite
end
