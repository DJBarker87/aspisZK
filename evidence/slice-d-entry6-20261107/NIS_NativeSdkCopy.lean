import NIS_SdkCopyFields
set_option autoImplicit false
namespace NIJ_NativeSdkCopy
open AspisR1.S2Trust

def Writes {W F : Type} (L : Library W F) (g : Guard) (source : Nat → UInt8)
 (start : Nat) : Nat → W → W → Prop
 | 0,w,after => after=w
 | n+1,w,after => ∃ before, Writes L g source start n w before ∧
   L.run before (.write g.token (start+n) (source (start+n)))=(after,.unit)

/-- The one-iteration SDK write law composes over arbitrary lengths and
pre-state. The SAME guard remains live; no copy-output equation is a premise. -/
theorem source {W F : Type} (L : Library W F) (sdk : S2TrustedSdkBorrow L)
 (w : W) (s : Heap F) (g : Guard) (bytes : Nat → UInt8) (start n : Nat)
 (related : L.related w s) (valid : Valid s) (found : lookup s g.token=some g)
 (exclusive : g.kind=.exclusive) (bounds : start+n≤(s.payload g.cell).descriptor.length) :
 ∃ after, Writes L g bytes start n w after ∧
 L.related after (NIJ_SdkWriteLoop.copy s g bytes start n) := by
 induction n with
 | zero => exact ⟨w,rfl,related⟩
 | succ n ih =>
   obtain ⟨before,history,rel⟩:=ih (by omega)
   let model:=NIJ_SdkWriteLoop.copy s g bytes start n
   have v : Valid model:=NIJ_SdkWriteLoop.valid s g bytes start n valid
   have live : lookup model g.token=some g := by
    rw [NIJ_SdkCopyFields.lookup];exact found
   have within : start+n<(model.payload g.cell).descriptor.length := by
    rw [NIJ_SdkWriteLoop.descriptor];omega
   obtain ⟨after,step,relAfter⟩:=
    (sdk.exclusive_deref before model g.token g rel v live exclusive).2
      (start+n) (bytes (start+n)) within
   exact ⟨after,⟨before,history,step⟩,relAfter⟩

/-- Canonical bulk heap equality, preserving the actual native operation
history. Existing SDK trust is retained rather than replaced by a new axiom. -/
theorem canonical {W F : Type} (L : Library W F) (sdk : S2TrustedSdkBorrow L)
 (w : W) (s : Heap F) (g : Guard) (src : Payload)
 (related : L.related w s) (valid : Valid s) (found : lookup s g.token=some g)
 (exclusive : g.kind=.exclusive) :
 ∃ after, Writes L g src.contents 0 (s.payload g.cell).descriptor.length w after ∧
 L.related after (AspisR1.S2W_TrustedStd.copyHeap s g.cell src) := by
 obtain ⟨after,history,rel⟩:=source L sdk w s g src.contents 0
   (s.payload g.cell).descriptor.length related valid found exclusive (by omega)
 rw [NIJ_SdkCopyCanonical.source] at rel
 exact ⟨after,history,rel⟩

#print axioms source
#print axioms canonical
end NIJ_NativeSdkCopy
