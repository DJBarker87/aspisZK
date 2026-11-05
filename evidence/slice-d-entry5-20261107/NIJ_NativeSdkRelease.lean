import NIJ_NativeSdkCopy
import NIJ_ExclusiveRelease
set_option autoImplicit false
namespace NIJ_NativeSdkRelease
open AspisR1.S2Trust AspisR1.S2W_D189Entry AspisR1.S2W_TrustedStd

theorem source {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
 (e : Entry) (w : W) (a : Nat) (src : Payload)
 (related : L.related w e.heap) (valid : Valid e.heap) :
 ∃ token owner acquired read written done,
  L.run w (.exclusive a token owner)=(acquired,.guard token) ∧
  L.run acquired (.deref token)=(read,.payload (e.heap.payload (e.heap.accounts a).1)) ∧
  NIJ_NativeSdkCopy.Writes L (NIJ_ExclusiveRelease.guard e.heap a token owner)
   src.contents 0 (e.heap.payload (e.heap.accounts a).1).descriptor.length read written ∧
  L.run written (.drop token)=(done,.unit) ∧
  L.related done (copyHeap e.heap (e.heap.accounts a).1 src) := by
 obtain ⟨token,owner,shared⟩:=NHJ_SdkDomains.enabled_exists e.heap a rfl
 have enabled : Enabled e.heap (.exclusive a token owner):=shared
 let s:=acquire e.heap (e.heap.accounts a).1 token owner .exclusive
 let g:=NIJ_ExclusiveRelease.guard e.heap a token owner
 have v : Valid s:=NIJ_ExclusiveEntry.entry_valid e a token owner valid enabled
 have found : lookup s token=some g:=NIJ_ExclusiveEntry.found e.heap a token owner
 obtain ⟨acquired,first,relA⟩:=sdk.exclusive_ok w e.heap a token owner related valid enabled rfl
 obtain ⟨read,second,relR⟩:=(sdk.exclusive_deref acquired s token g relA v found rfl).1
 obtain ⟨written,history,relW⟩:=NIJ_NativeSdkCopy.source L sdk read s g src.contents 0
   (e.heap.payload (e.heap.accounts a).1).descriptor.length relR v found rfl (by simp [s,g,acquire,NIJ_ExclusiveRelease.guard])
 let copied:=NIJ_SdkWriteLoop.copy s g src.contents 0 (e.heap.payload (e.heap.accounts a).1).descriptor.length
 have copiedValid : Valid copied:=NIJ_SdkWriteLoop.valid s g src.contents 0 _ v
 have copiedFound : lookup copied token=some g := by
  rw [NIJ_SdkCopyFields.lookup];exact found
 have copiedCounter : copied.counter g.cell = -1 := by
  rw [NIJ_SdkCopyFields.counter]
  exact NIJ_ExclusiveEntry.counter e.heap a token owner
 obtain ⟨done,last,relD⟩:=sdk.exclusive_drop written copied token g relW copiedValid copiedFound rfl copiedCounter
 have released : release copied g=copyHeap e.heap (e.heap.accounts a).1 src := by
  rw [NIJ_ExclusiveRelease.copied e.heap a token owner src.contents 0 _ (by rfl) (by rfl)]
  exact NIJ_SdkCopyCanonical.source e.heap g src
 rw [released] at relD
 exact ⟨token,owner,acquired,read,written,done,first,second,history,last,relD⟩

#print axioms source
end NIJ_NativeSdkRelease
