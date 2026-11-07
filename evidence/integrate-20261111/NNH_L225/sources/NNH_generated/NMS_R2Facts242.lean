import NMS_R2AuthFacts
set_option autoImplicit false
namespace NMS_R2Facts242
open RSL NMS_R2Refine
/-- Exact successful scanner guarantee exported by CLOSED TX2:226. This
local child-model property still needs its concrete carrier installation. -/
def ScannerExtent (L : PoolLib) : Prop :=
 ∀ bytes env scanned events,
 L.scanProof bytes env ⟨.ret (.ok scanned),events⟩ → scanned.2 = PROOF_BYTES

theorem successful (L : PoolLib) (D : DeployedIds) (scan : ScannerExtent L)
 (a : TX2_242.Args) (env : Env) (validated : TX2_242.Validated L) (events : List Event)
 (run : TX2_242.Ref L D a env ⟨.ret (.ok validated),events⟩) :
 validated.proof_length = PROOF_BYTES ∧ a.accounts.length = 7 ∧
 ∃ v, a.accounts[6]? = some v ∧ v.length = .ok CHECKPOINT_BYTES := by
 unfold TX2_242.Ref at run
 obtain ⟨_,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨q,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨_,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨lane,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨slot,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨auth,_,_,hauth,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨proofAccount,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨bytes,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨scanned,_,_,hscan,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨statement,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 have final := Except.ok.inj (Exit.ret.inj (congrArg Obs.exit run))
 have length : validated.proof_length = scanned.2 := congrArg TX2_242.Validated.proof_length final
 refine ⟨length.trans (scan bytes env scanned _ hscan), ?_⟩
 exact NMS_R2AuthFacts.checkpoint L D _ env auth _ hauth.2

#print axioms successful
end NMS_R2Facts242
