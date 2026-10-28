import NBH_Audit
import S2K_DigestBytes
set_option autoImplicit false
noncomputable section
namespace NBN_OutputLane
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_forest_accounts
abbrev Digest := Array U32 8#usize

def first (d : Digest) : U8 := (DigestBytes.bytes d).val[0]!

theorem first_source (d : Digest) : first_canonical_byte d = ok (first d) := by
  unfold first_canonical_byte
  rw [DigestBytes.exact]
  simp [Array.index_usize,first,(DigestBytes.bytes d).property]

def result (d : Digest) : core.result.Result U8 PoolV1PairForestAccountErrorV1 :=
  if NBD_DigestInduction.Canonical d then .Ok (first d &&& 7#u8)
  else .Err .NonCanonicalDigest

theorem source (d : Digest) : pool_v1_pair_forest_output_lane_v1 d = ok (result d) := by
  unfold pool_v1_pair_forest_output_lane_v1
  rw [NBD_DigestInduction.same_scanner,NBD_DigestInduction.source]
  simp only [bind_tc_ok]
  by_cases h : NBD_DigestInduction.Canonical d
  · simp only [h,decide_true,if_true,first_source,bind_tc_ok,lift,result]
    simp [h]
  · simp [h,result]

#print axioms first_source
#print axioms source
end NBN_OutputLane
