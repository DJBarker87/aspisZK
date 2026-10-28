import NBN_EncoderDomains
set_option autoImplicit false
noncomputable section
namespace NBN_EncoderBytes
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

def tag : Statement → U8
  | .PrivateTransfer _ _ => 1#u8
  | .Withdrawal _ _ => 2#u8

def commonBytes (s : Statement) : List U8 :=
  AspisS6OuterByteLayout.common_prefix (fromPoolV1PairForestTerminalCommonV1 (common s)) (tag s)

def bytes (s : Statement) (pay : Array U8 216#usize) : Array U8 1880#usize :=
  ⟨(commonBytes s ++ (NBN_LateTail.value (common s).lane_transition NBN_LateResult.header).val) ++ pay.val, by
    have p := AspisS6OuterByteLayout.common_length (fromPoolV1PairForestTerminalCommonV1 (common s)) (tag s)
    have l := (NBN_LateInvariant.value_length (common s).lane_transition NBN_LateResult.header).trans NBN_LateResult.header_length
    have q := pay.property
    change pay.val.length = 216 at q
    change (NBN_LateTail.value (common s).lane_transition NBN_LateResult.header).val.length = 1520 at l
    change (commonBytes s).length = 144 at p
    simp only [List.length_append,p,l,q]
    rfl⟩

theorem length (s : Statement) (pay : Array U8 216#usize) : (bytes s pay).val.length = 1880 :=
  (bytes s pay).property

#print axioms length
end NBN_EncoderBytes
