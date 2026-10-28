import NBN_DigestResultDependency
import NBN_OutputLane
set_option autoImplicit false
noncomputable section
namespace NBN_FirstByteDependency
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open NBN_DigestResultDependency
attribute [local instance] Classical.propDecidable

def first (encode : Encode) (d : Digest) : Result U8 := do
  let bytes ← encode d
  Array.index_usize bytes 0#usize

def lane (encode : Encode) (d : Digest) :
    Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :=
  if NBD_DigestInduction.Canonical d then do
    let b ← first encode d
    ok (.Ok (b &&& 7#u8))
  else ok (.Err .NonCanonicalDigest)

theorem first_source (encode : Encode) (lower : NBN_Dep_DigestEncodeRaw encode) (d : Digest) :
    first encode d = pool_v1.pair_forest_accounts.first_canonical_byte d := by
  unfold first pool_v1.pair_forest_accounts.first_canonical_byte
  rw [lower d,DigestBytes.exact]

theorem lane_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode) (d : Digest) :
    lane encode d = pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d := by
  rw [NBN_OutputLane.source]
  by_cases good : NBD_DigestInduction.Canonical d
  · simp only [lane,good,if_true,first,lower d good,bind_tc_ok]
    simp [Array.index_usize,(DigestBytes.bytes d).property,NBN_OutputLane.result,good,NBN_OutputLane.first]
  · simp [lane,good,NBN_OutputLane.result]

#print axioms first_source
#print axioms lane_source
end NBN_FirstByteDependency
