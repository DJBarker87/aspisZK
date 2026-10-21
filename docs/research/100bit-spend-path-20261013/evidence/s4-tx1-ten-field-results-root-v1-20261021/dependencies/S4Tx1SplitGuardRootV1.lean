import Tx1OpsCut
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx1SplitGuardRootV1
open AspisR1CurrentCaller AspisR1CallerV4Tx1OpsCut

/-- The admitted source constant in compact.rs is 10. -/
def withFrozenSplit {H : Type} (ops : Ops H) : Ops H := { ops with split := 10#usize }

theorem tx1_success_requires_split {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec Std.U8)
    (h : tx1 ops inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = ops.split := by
  by_contra hk
  simp [tx1, hk] at h

theorem frozen_tx1_success_requires_ten {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec Std.U8)
    (h : tx1 (withFrozenSplit ops) inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize :=
  tx1_success_requires_split (withFrozenSplit ops) inst public1 public_bytes proof k hash obs bytes h

#print axioms tx1_success_requires_split
#print axioms frozen_tx1_success_requires_ten
end AspisR1S4Tx1SplitGuardRootV1
