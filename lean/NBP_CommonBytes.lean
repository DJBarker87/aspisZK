import NBP_CommonTail0
set_option autoImplicit false
noncomputable section
namespace NBP_CommonBytes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
abbrev encoded := NBP_CommonTail0.expected

theorem association (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c =
      NBP_CommonTail0.run output magic kind c := by
  unfold pool_v1.payment_relation.encode_common
  unfold NBP_CommonTail0.run NBP_CommonTail1.run NBP_CommonTail2.run NBP_CommonTail3.run NBP_CommonTail4.run NBP_CommonTail5.run NBP_CommonTail6.run
  rfl
theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c = ok (encoded output magic kind c) := by
  rw [association]
  exact NBP_CommonTail0.result output magic kind c
#print axioms association
#print axioms result
end NBP_CommonBytes
