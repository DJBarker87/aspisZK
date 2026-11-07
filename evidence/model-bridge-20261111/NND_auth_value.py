from pathlib import Path
E=Path(__file__).resolve().parent
s=(E.parent/'rowspec-lead-20261107/RSL_TX2_233.lean').read_text()
prefix='''import NND_RegistryEval
import NND_LaneReturned
import RSL_TX2_233
set_option autoImplicit false
namespace NND_AuthEval
open RSL RSL.TX2_233 NND_Returned
'''
for a,b in [('body','bodyValue'),('Ref','value')]:
 t=s[s.index('def '+a+' '):];t=t[:t.index('\n\n')]
 t=t.replace('def '+a+' ','def '+b+' ').replace(': RS Authenticated', '(env : Env) : Except ProgramError Authenticated')
 t=t.replace('Spec.call TX2_234.Domain (TX2_234.Ref L D)\n            ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩','NND_RegistryEval.value L D ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩ env')
 t=t.replace('Spec.call TX2_217.Domain TX2_217.Ref ldata','NND_LaneReturned.value ldata').replace('body L D a p m c l r e v','bodyValue L D a p m c l r e v env')
 for x,y in [('RS.bind','ebind'),('RS.seq','eseq'),('RS.check','echeck'),('RS.ofExcept','id'),('RS.ofOption','option'),('RS.pure','Except.ok'),('RS.throw','Except.error'),('pdaOrErr','NND_RegistryEval.pdaValue env'),('decodeMasterBox L mdata','option (L.decodeMaster mdata) .invalidAccountData'),('decodeCheckpointBox L cdata','option (L.decodeCheckpoint cdata) .invalidAccountData'),('RS.lift Spec.alloc','Except.ok ()')]:t=t.replace(x,y)
 
 if a=='body':
  start=t.index('  Except.ok { master_account')
  t=t[:start]+'  Except.ok { master_account := m.key, checkpoint_account := c.key, selected_lane_account := l.key, master := master, checkpoint := ck, selected_lane := lane, live_snapshot := { pool := m.key, deployment_domain := master.identity.deployment_domain, sequence := lane.tree.next_leaf_index, next_pair_index := lane.tree.next_leaf_index, current_root := lane.tree.root, frontier := lane.tree.frontier } }'
 prefix+='\n'+t+'\n'
prefix+='''
theorem pda_guard (env : Env) (bad : Bool) (seeds : List Bytes) (program expected : B32) :
 Returns (if bad then RS.throw .invalidAccountData else
  RS.bind (RSL.pdaOrErr seeds program) (fun k => RS.check (decide (k ≠ expected)) .invalidAccountData)) env
 (if bad then Except.error .invalidAccountData else
  ebind (NND_RegistryEval.pdaValue env seeds program) (fun k => echeck (decide (k ≠ expected)) .invalidAccountData)) := by
 cases bad
 · exact rs_bind _ _ env _ _ (NND_Returned.pdaOrErr env _ _) (fun k => check env _ _)
 · exact throw env _

theorem body_returned (L : PoolLib) (D : DeployedIds) (a : Args)
 (p m c l r e v : OwnedAccount) (env : Env) :
 Returns (body L D a p m c l r e v) env (bodyValue L D a p m c l r e v env) := by
 unfold body bodyValue
 apply seq _ _ env _ _ (ofExcept env _)
 apply seq _ _ env _ _ (ofExcept env _)
 apply seq _ _ env _ _ (ofExcept env _)
 apply seq _ _ env _ _ (ofExcept env _)
 apply seq _ _ env _ _ (ofExcept env _)
 apply seq _ _ env _ _ (ofExcept env _)
 apply rs_bind _ _ env _ _ (ofExcept env _)
 intro mdata
 apply rs_bind _ _ env _ _ (masterBox L env mdata)
 intro master
 apply seq _ _ env _ _ (pda_guard env _ _ _ _)
 apply seq _ _ env _ _ (call _ _ _ env _ (NND_RegistryEval.returned L D _ env))
 apply rs_bind _ _ env _ _ (ofExcept env _)
 intro cdata
 apply rs_bind _ _ env _ _ (checkpointBox L env cdata)
 intro ck
 apply seq _ _ env _ _ (pda_guard env _ _ _ _)
 apply rs_bind _ _ env _ _ (ofExcept env _)
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
end NND_AuthEval
'''
(E/'NND_AuthEval.lean').write_text(prefix)
