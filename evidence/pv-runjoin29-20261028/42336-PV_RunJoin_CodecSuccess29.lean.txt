import R1Z.PV_RunJoin_CodecPrefixDomain29
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CodecSuccess29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder.pool_v1.pair_tree_profile

def Path (bytes : Slice U8) : Prop := R1Z.PV_RunJoin_CodecPrefixDomain29.Path bytes

theorem iff_path (bytes : Slice U8) :
    (∃ snapshot, decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok snapshot)) ↔ Path bytes := by
  rw [← R1Z.PV_RunJoin_DecoderPrefix29.source]
  exact R1Z.PV_RunJoin_CodecPrefixDomain29.success_iff bytes
#print axioms iff_path
end R1Z.PV_RunJoin_CodecSuccess29
