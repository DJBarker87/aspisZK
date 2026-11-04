import NFT_ZeroPhysical
set_option autoImplicit false
namespace NFT_ZeroJoin
open Aeneas Aeneas.Std Result

/-- Same original input, every reached suffix and allocation identity, with the
complete Result equality from the established finite-loop induction. No child
success, selected output, physical-result law or independent execution is a hypothesis. -/
theorem source_and_frame {A : Type} (allocation : A) (bytes : Slice U8)
    (bound : bytes.val.length≤4096) :
    _root_.AdapterRw.r1_pool_adapter.owned.require_zero bytes=
      (do let b ← NFQ_ScanReference.zero_ref bytes;ok (NFQ_ZeroSource.result b)) ∧
    ∀ i : Nat, i≤bytes.val.length →
      let surface : NFT_ZeroPhysical.Surface A := ⟨allocation,bytes.val,i⟩
      (NFT_ZeroPhysical.pad bytes.val).length=4096 ∧
      ((NFT_ZeroPhysical.pad bytes.val).drop i).take (bytes.val.length-i)=NFT_ZeroPhysical.view surface ∧
      NFT_ZeroPhysical.pointer surface=(allocation,i) ∧
      NFT_ZeroPhysical.pointer (NFT_ZeroPhysical.advance surface)=(allocation,i+1) ∧
      NFT_ZeroPhysical.view (NFT_ZeroPhysical.advance surface)=(NFT_ZeroPhysical.view surface).drop 1 ∧
      (NFT_ZeroPhysical.advance surface).bytes=bytes.val := by
  refine ⟨NFQ_ZeroSource.source bytes bound,?_⟩
  intro i inside
  exact ⟨NFT_ZeroPhysical.pad_length _ bound,NFT_ZeroPhysical.suffix_pad _ _ inside,
    rfl,rfl,NFT_ZeroPhysical.slice_step _,rfl⟩

/-- The deployed owned caller admits the S2 checkpoint, 1768 bytes, before
borrowing it; the approved same-account SDK view law transports that size. -/
theorem checkpoint_bound (length : Nat) (same_checkpoint : length=1768) : length≤4096 := by omega

#print axioms source_and_frame
#print axioms checkpoint_bound
end NFT_ZeroJoin
