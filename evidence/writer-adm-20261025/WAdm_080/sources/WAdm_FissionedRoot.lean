import WAdm_FissionedContent
import WAdm_WeightsHelpers
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_FissionedRoot
open WAdm_Fissioned WAdm_model WAdm_EmittedScalars WAdm_FissionedContent
open AspisR1Stage2.WireTx2 (singletonParts checksumParts checksumDomain)

theorem append (out : alloc.vec.Vec U8) (s : Slice U8)
    (bound : out.val.length + s.val.length ≤ Usize.max) :
    ∃ after, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s = ok after ∧
      after.val = out.val ++ s.val := ⟨_,WAdm_VecStd.extend out s bound,rfl⟩

theorem emitted {H : Type} (D : WAdm_Fissioned.aspis_core.digest.Digest32 H) (hash : H)
    (f : WAdm_Fields) (weights : alloc.vec.Vec K) (proof pub : Slice U8)
    (size : weights.val.length = 64) (hp hu hc : Array U8 32#usize)
    (hpCall : D.digest hash (singletonParts proof) = ok hp)
    (huCall : D.digest hash (singletonParts pub) = ok hu)
    (hcCall : D.digest hash (checksumParts (bodySlice f weights hp hu size)) = ok hc) :
    WAdm_checkpoint D f weights proof pub hash = ok (finish f weights hp hu hc size) := by
  let out0 := alloc.vec.Vec.with_capacity U8 1768#usize
  let magic : Array U8 8#usize := Array.make 8#usize [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8]
  let flags : Array U8 8#usize := Array.make 8#usize [2#u8,10#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
  have n0 : out0.val.length = 0 := rfl
  obtain ⟨v1,c1,e1⟩ := append out0 magic.to_slice (by change out0.val.length + magic.val.length ≤ Usize.max; rw [n0,magic.property]; scalar_tac)
  have n1 : v1.val.length = 8 := by rw [e1,List.length_append,n0]; exact magic.property
  obtain ⟨v2,c2,e2⟩ := append v1 flags.to_slice (by change v1.val.length + flags.val.length ≤ Usize.max; rw [n1,flags.property]; scalar_tac)
  have n2 : v2.val.length = 16 := by rw [e2,List.length_append,n1]; have := flags.property; omega
  obtain ⟨v3,c3,e3⟩ := append v2 hp.to_slice (by change v2.val.length + hp.val.length ≤ Usize.max; rw [n2,hp.property]; scalar_tac)
  have n3 : v3.val.length = 48 := by rw [e3,List.length_append,n2]; have := hp.property; omega
  obtain ⟨v4,c4,e4⟩ := append v3 hu.to_slice (by change v3.val.length + hu.val.length ≤ Usize.max; rw [n3,hu.property]; scalar_tac)
  have n4 : v4.val.length = 80 := by rw [e4,List.length_append,n3]; have := hu.property; omega
  obtain ⟨v5,c5,e5⟩ := append v4 f.state.to_slice (by change v4.val.length + f.state.val.length ≤ Usize.max; rw [n4,f.state.property]; scalar_tac)
  have n5 : v5.val.length = 112 := by rw [e5,List.length_append,n4]; have := f.state.property; omega
  have lr := WAdm_ArrayHelpers.flatMap_length (fun x : Array U8 32#usize => x.val) 32 (fun x => x.property) f.roots.val
  have le := WAdm_ArrayHelpers.flatMap_length CheckpointBytesE.rawBytes 32 CheckpointBytesE.rawBytes_length f.early.val
  have lq := WAdm_ArrayHelpers.flatMap_length (fun x => (core.num.U32.to_le_bytes x).val) 4 (fun x => (core.num.U32.to_le_bytes x).property) f.queries.val
  have ls := WAdm_ArrayHelpers.flatMap_length CheckpointP6EncodeK.bytes 16 k_length f.semantic.val
  have lz := WAdm_ArrayHelpers.flatMap_length CheckpointP6EncodeK.bytes 16 k_length f.coordinates.val
  have lt := WAdm_ArrayHelpers.flatMap_length CheckpointBytesE.rawBytes 32 CheckpointBytesE.rawBytes_length f.tail.val
  have lw := WAdm_ArrayHelpers.flatMap_length CheckpointP6EncodeK.bytes 16 k_length weights.val
  obtain ⟨v6,c6,e6⟩ := WAdm_ArrayHelpers.roots f.roots v5 (by rw [n5]; scalar_tac)
  have n6 : v6.val.length = 176 := by rw [e6,List.length_append,n5,lr,f.roots.property]; rfl
  obtain ⟨v7,c7,e7⟩ := WAdm_ArrayHelpers.early f.early v6 (by rw [n6]; scalar_tac)
  have n7 : v7.val.length = 304 := by rw [e7,List.length_append,n6,le,f.early.property]; rfl
  obtain ⟨v8,c8,e8⟩ := put_k v7 f.rho (by rw [n7]; scalar_tac)
  have n8 : v8.val.length = 320 := by rw [e8,List.length_append,n7,k_length]
  obtain ⟨v9,c9,e9⟩ := WAdm_ArrayHelpers.queries f.queries v8 (by rw [n8]; scalar_tac)
  have n9 : v9.val.length = 408 := by rw [e9,List.length_append,n8,lq,f.queries.property]; rfl
  obtain ⟨v10,c10,e10⟩ := WAdm_ArrayHelpers.semantic f.semantic v9 (by rw [n9]; scalar_tac)
  have n10 : v10.val.length = 568 := by rw [e10,List.length_append,n9,ls,f.semantic.property]; rfl
  obtain ⟨v11,c11,e11⟩ := WAdm_ArrayHelpers.coordinates f.coordinates v10 (by rw [n10]; scalar_tac)
  have n11 : v11.val.length = 632 := by rw [e11,List.length_append,n10,lz,f.coordinates.property]; rfl
  obtain ⟨v12,c12,e12⟩ := WAdm_ArrayHelpers.tail f.tail v11 (by rw [n11]; scalar_tac)
  have n12 : v12.val.length = 696 := by rw [e12,List.length_append,n11,lt,f.tail.property]; rfl
  obtain ⟨v13,c13,e13⟩ := put_k v12 f.power (by rw [n12]; scalar_tac)
  have n13 : v13.val.length = 712 := by rw [e13,List.length_append,n12,k_length]
  obtain ⟨v14,c14,e14⟩ := WAdm_WeightsHelpers.weights weights v13 (by rw [n13,size]; scalar_tac)
  have n14 : v14.val.length = 1736 := by rw [e14,List.length_append,n13,lw,size]
  have bodyVal : v14.val = body f weights hp hu := by
    rw [e14,e13,e12,e11,e10,e9,e8,e7,e6,e5,e4,e3,e2,e1]
    rfl
  have bodyEq : v14.deref = bodySlice f weights hp hu size := Subtype.ext bodyVal
  have hcNative : D.digest hash (checksumParts v14.deref) = ok hc := by rw [bodyEq]; exact hcCall
  obtain ⟨v15,c15,e15⟩ := append v14 hc.to_slice (by change v14.val.length + hc.val.length ≤ Usize.max; rw [n14,hc.property]; scalar_tac)
  have n15 : v15.val.length = 1768 := by rw [e15,List.length_append,n14]; have := hc.property; omega
  have finalEq : v15 = finish f weights hp hu hc size := by
    apply Subtype.ext
    change v15.val = body f weights hp hu ++ hc.val
    rw [e15,bodyVal]
  have wl : alloc.vec.Vec.len weights = 64#usize := UScalar.eq_of_val_eq size
  have ol : alloc.vec.Vec.len v15 = 1768#usize := UScalar.eq_of_val_eq n15
  change D.digest hash (Array.to_slice (Array.make 1#usize [proof])) = ok hp at hpCall
  change D.digest hash (Array.to_slice (Array.make 1#usize [pub])) = ok hu at huCall
  change D.digest hash (Array.to_slice (Array.make 2#usize [checksumDomain,v14.deref])) = ok hc at hcNative
  dsimp only [out0,magic,flags] at c1 c2
  unfold WAdm_checkpoint
  simpa only [wl,ol,massert,if_pos rfl,lift,bind_tc_ok,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,
    hpCall,huCall,hcNative] using congrArg Result.ok finalEq

#print axioms append
#print axioms emitted
end AspisR1.WAdm_FissionedRoot
end
