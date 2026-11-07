import NMV_NoWritePool
set_option autoImplicit false
namespace NMV_NoWriteOwned
open RSL NMV_NoWrite NMV_NoWritePool

syntax "owned_free" "(" term "," term ")" : tactic
macro_rules
 | `(tactic| owned_free ($pl:term, $hw:term)) => `(tactic|
 first
 | exact ($pl).scan _
 | exact ($pl).reconstruct _ _ _
 | exact ($pl).encode _
 | exact ($pl).emit _
 | exact ($hw) _ _ _
 | exact auth_free _ _ ($pl) _
 | exact validate_free _ _ ($pl) _
 | exact pda_free _ _
 | exact registry_free _ _ _
 | exact lane_free _
 | exact master_free _ _
 | exact checkpoint_free _ _
 | exact pure_free _
 | exact alloc_free
 | exact panic_free
 | exact env_free _
 | exact ofExcept_free _
 | exact ofOption_free _ _
 | exact check_free _ _
 | exact index_free _ _
 | apply lift_free; owned_free ($pl, $hw)
 | apply call_free; owned_free ($pl, $hw)
 | apply rs_seq_free <;> owned_free ($pl, $hw)
 | apply rs_bind_free
   · owned_free ($pl, $hw)
   · intro _; owned_free ($pl, $hw)
 | apply bind_free
   · owned_free ($pl, $hw)
   · intro _; owned_free ($pl, $hw)
 | apply emit_free; intro c b h; cases h
 | split <;> owned_free ($pl, $hw))

theorem auth_body_free (L : PoolLib) (D : DeployedIds) (pl : PoolLaws L)
 (a : TX2_233.Args) (p m c l r e v : OwnedAccount) :
 Free (TX2_233.body L D a p m c l r e v) := by
 unfold TX2_233.body
 owned_free (pl, (fun (_ _ _ : Bytes) => pure_free ()))

theorem auth_free (L : PoolLib) (D : DeployedIds) (pl : PoolLaws L) (a : TX2_233.Args) :
 Free (TX2_233.Ref L D a) := by
 unfold TX2_233.Ref
 split
 · exact auth_body_free L D pl _ _ _ _ _ _ _ _
 · exact pure_free _

theorem validate_free (L : PoolLib) (D : DeployedIds) (pl : PoolLaws L) (a : TX2_242.Args) :
 Free (TX2_242.Ref L D a) := by
 unfold TX2_242.Ref
 apply rs_seq_free _ _ (check_free _ _)
 apply rs_bind_free _ _ (ofOption_free _ _)
 intro q
 apply rs_seq_free _ _ (check_free _ _)
 apply rs_bind_free _ _ (ofOption_free _ _)
 intro lane
 apply rs_bind_free _ _ (ofExcept_free _)
 intro slot
 apply rs_bind_free
 · exact call_free _ _ _ (auth_free L D pl _)
 · intro auth
   apply rs_bind_free _ _ (ofOption_free _ _)
   intro acc
   apply rs_bind_free _ _ (ofExcept_free _)
   intro pdata
   apply rs_bind_free _ _ (pl.scan pdata)
   intro scanned
   apply rs_bind_free _ _ (pl.reconstruct q auth scanned.1)
   intro statement
   exact pure_free _

#print axioms auth_body_free
#print axioms auth_free
#print axioms validate_free
end NMV_NoWriteOwned
