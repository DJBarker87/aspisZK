import R1Z.PV_Inv_HeadlinePole
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_CouplingPole
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
open PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {K CommitHandle Aux Bat Adv W S : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [Zero W] [DecidableEq W]

/-- Same-coin containment in the EXISTING poleBad, with its P conjunct retained.
For the headline toCoins must be the original coupling's middle coin projection.
No independent draw, new union member or new probability allowance is used. -/
theorem contained (P : Challenges K → Prop) (h : HonestProver K)
    (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv) (x : Statement K CommitHandle)
    (w : h.Instance) (toCoins : S → Fin ab.N → ab.Coins)
    (banks : S → Fin ab.N → Banks K) (join : ∀ u k, P_banks (banks u k) (h.build w))
    (weight : SourceLink K → W) (registry : List (SourceLink K)) (enumeration : P_registry registry)
    (state : S → Fin ab.N → State Key K W)
    (run : ∀ u k, PV_Inv_GlobalSlots.run (empty 0)
      (entries (banks u k) ((ab.draw adv x (toCoins u k)).sem 0) weight registry)=some (state u k))
    (u : S) (zero : ∃ k, P (ab.draw adv x (toCoins u k)) ∧
      PV_Inv_RegistryZeroEvent.zeroEvent ((ab.draw adv x (toCoins u k)).sem 1) (state u k)) :
    poleBad P h (MaskImageVR1.VR1 h) ab adv x w (toCoins u) := by
  obtain ⟨k,hp,hz⟩ := zero
  exact ⟨k,PV_Inv_HeadlinePole.attempt_contained P h ab adv x w (toCoins u k)
    (banks u k) (join u k) weight registry enumeration (state u k) (run u k) hp hz⟩

#print axioms contained
end R1Z.PV_Inv_CouplingPole
