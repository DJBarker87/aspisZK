import NNH_ReturnedClone
import NNH_RegistryEval
import NND_LaneReturned
import RSL_TX2_233
set_option autoImplicit false
namespace NNH_AuthEval
open RSL RSL.TX2_233 NND_Returned

def bodyValue (L : PoolLib) (D : DeployedIds) (a : Args)
    (p m c l r e v : OwnedAccount) (env : Env) : Except ProgramError Authenticated :=
  let pool := a.pool_program
  eseq (id (readonlyBuffer p)) <|
  eseq (id (NNH_ReturnedClone.checkpointValue v a.verifier_program false)) <|
  eseq (id (readonlyAccount m pool)) <|
  eseq (id (readonlyAccount c pool)) <|
  eseq (id (readonlyAccount l pool)) <|
  eseq (id (requireDistinct [p, m, c, l, r, e, v])) <|
  -- master (lines 261-275); `||` short-circuits the PDA syscall
  ebind (id m.bytes) fun mdata =>
  ebind (option (L.decodeMaster mdata) .invalidAccountData) fun master =>
  eseq (if decide (master.identity.pool ≠ m.key) || master.initialized_lane_mask != ALL_LANES_MASK
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_MASTER, master.identity.asset_mint.bytes, [master.bump]] pool)
                 fun k => echeck (decide (k ≠ m.key)) .invalidAccountData) <|
  -- registry (lines 276-284): OPEN child TX2:234 at SAME arguments
  eseq (NNH_RegistryEval.value L D ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩ env) <|
  -- checkpoint (lines 286-301)
  ebind (id c.bytes) fun cdata =>
  ebind (option (L.decodeCheckpoint cdata) .invalidAccountData) fun ck =>
  eseq (if decide (ck.master ≠ m.key)
             || decide (ck.deployment_domain ≠ master.identity.deployment_domain)
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_CHECKPOINT, m.key.bytes, u64le ck.checkpoint_sequence,
                                  [ck.bump]] pool)
                 fun k => echeck (decide (k ≠ c.key)) .invalidAccountData) <|
  -- selected lane (lines 302-317): OPEN child TX2:217 at SAME argument
  ebind (id l.bytes) fun ldata =>
  ebind (NND_LaneReturned.value ldata) fun lane =>
  eseq (if decide (lane.master ≠ m.key) || lane.lane_id != a.output_lane
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_LANE, m.key.bytes, [a.output_lane], [lane.bump]] pool)
                 fun k => echeck (decide (k ≠ l.key)) .invalidAccountData) <|
  -- live snapshot Box (lines 318-325) and the returned owner (326-334)
  eseq (Except.ok ()) <|
  Except.ok { master_account := m.key, checkpoint_account := c.key, selected_lane_account := l.key, master := master, checkpoint := ck, selected_lane := lane, live_snapshot := { pool := m.key, deployment_domain := master.identity.deployment_domain, sequence := lane.tree.next_leaf_index, next_pair_index := lane.tree.next_leaf_index, current_root := lane.tree.root, frontier := lane.tree.frontier } }

def value (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) : Except ProgramError Authenticated :=
  match a.accounts with
  | [p, m, c, l, r, e, v] => bodyValue L D a p m c l r e v env
  | _ => Except.error (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument)

theorem pda_guard (env : Env) (bad : Bool) (seeds : List Bytes) (program expected : B32) :
 Returns (if bad then RS.throw .invalidAccountData else
  RS.bind (RSL.pdaOrErr seeds program) (fun k => RS.check (decide (k ≠ expected)) .invalidAccountData)) env
 (if bad then Except.error .invalidAccountData else
  ebind (NNH_RegistryEval.pdaValue env seeds program) (fun k => echeck (decide (k ≠ expected)) .invalidAccountData)) := by
 cases bad
 · exact rs_bind _ _ env _ _ (NND_Returned.pdaOrErr env _ _) (fun k => check env _ _)
 · exact throw env _

theorem body_returned (L : PoolLib) (D : DeployedIds) (a : Args)
 (p m c l r e v : OwnedAccount) (env : Env) :
 Returns (body L D a p m c l r e v) env (bodyValue L D a p m c l r e v env) := by
 unfold body bodyValue
 apply seq _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 apply seq _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 apply seq _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 apply seq _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 apply seq _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 apply seq _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro mdata
 apply rs_bind _ _ env _ _ (masterBox L env mdata)
 intro master
 apply seq _ _ env _ _ (pda_guard env _ _ _ _)
 apply seq _ _ env _ _ (call _ _ _ env _ (NNH_RegistryEval.returned L D _ env))
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro cdata
 apply rs_bind _ _ env _ _ (checkpointBox L env cdata)
 intro ck
 apply seq _ _ env _ _ (pda_guard env _ _ _ _)
 apply rs_bind _ _ env _ _ (by first | exact NNH_ReturnedClone.ofCloned env _ | exact NNH_ReturnedClone.checkpoint_returned env _ _ _ | exact ofExcept env _)
 intro ldata
 apply rs_bind _ _ env _ _ (call _ _ _ env _ (NND_LaneReturned.returned ldata env))
 intro lane
 apply seq _ _ env _ _ (pda_guard env _ _ _ _)
 apply seq _ _ env _ _ (rs_lift _ env _ (alloc env))
 exact rs_pure env _

theorem returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (Ref L D a) env (value L D a env) := by
 unfold Ref value
 split
 · rename_i p m c l r e v h
   simp only [h]
   exact body_returned L D a p m c l r e v env
 · rename_i h
   have hv : value L D a env = Except.error (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument) := by
    unfold value
    split
    · rename_i p m c l r e v heq
      exact False.elim (h p m c l r e v heq)
    · rfl
   change Returns (RS.throw _) env (value L D a env)
   rw [hv]
   exact throw env _

#print axioms pda_guard
#print axioms body_returned
#print axioms returned
end NNH_AuthEval
