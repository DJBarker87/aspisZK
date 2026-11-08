import NMX_R6_Children
import NMX_R6_Clone
import NMX_R4_NMS242Instantiation
set_option autoImplicit false
noncomputable section
namespace NMX_R6_Port242
open RSL NMX_R6_Observation
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed

def pure {A : Type} (r : Except ProgramError A) : Obs (Except ProgramError A) := ⟨.ret r,[]⟩
def fromOption {A : Type} (x : Option A) (e : ProgramError) := pure (match x with | some a => .ok a | none => .error e)

def suffix (q : L.Request) (a : Authenticated) (accounts : List OwnedAccount) :
 Obs (Except ProgramError (TX2_242.Validated L)) :=
 rsbind (fromOption accounts.head? .notEnoughAccountKeys) fun proofAccount =>
 rsbind (pure proofAccount.bytes) fun data =>
 rsbind (NMX_R6_Children.scan data) fun scanned =>
 rsbind (NMX_R6_Children.reconstruct q a scanned.1) fun statement =>
 pure (.ok ⟨statement,scanned.2⟩)

def validate (choices : NMX_R4_Authentication.Choices) (a : TX2_242.Args) (env : Env) :
 Obs (Except ProgramError (TX2_242.Validated L)) :=
 if a.instruction_data.length != REQUEST_BYTES then pure (.error .invalidInstructionData) else
 rsbind (fromOption (L.decodeRequest a.instruction_data) .invalidInstructionData) fun q =>
 if NMX_R5_Request242.bad q then pure (.error .invalidInstructionData) else
 rsbind (fromOption (L.outputLane (L.reqNullifier q)) .invalidInstructionData) fun lane =>
 rsbind (pure a.current_slot) fun slot =>
 rsbind (NMX_R4_Authentication.authenticate choices
  ⟨a.verifier_program,a.accounts,L.reqPoolProgram q,lane,slot⟩ env) fun auth =>
 suffix q auth a.accounts

theorem fromOption_member {A : Type} (x : Option A) (e : ProgramError) (env : Env) :
 RS.ofOption x e env (fromOption x e) := by
 cases x <;> rfl

theorem suffix_member (q : L.Request) (a : Authenticated) (accounts : List OwnedAccount) (env : Env) :
 NMX_R5_AfterAuth242.model q a accounts env (suffix q a accounts) := by
 unfold NMX_R5_AfterAuth242.model suffix
 apply rsmember _ _ env _ _ (fromOption_member _ _ env)
 intro proofAccount
 apply rsmember _ _ env _ _ (NMX_R6_Clone.member _ env)
 intro data
 apply rsmember _ _ env _ _ (NMX_R6_Children.scan_member data env)
 intro scanned
 apply rsmember _ _ env _ _ (NMX_R6_Children.reconstruct_member q a scanned.1 env)
 intro statement
 rfl

/-- Total source-control port: literal length/decoder/guard/lane/slot/auth/data/
scan/reconstruction order. No endpoint witness is chosen from Ref. -/
theorem replay_member (choices : NMX_R4_Authentication.Choices) (a : TX2_242.Args) (env : Env) :
 NMX_R4_NMSFold242.replay L D (NMX_R4_Authentication.authenticate choices) a env
  (validate choices a env) := by
 unfold validate NMX_R4_NMSFold242.replay
 split
 · rename_i reject
   rw [reject,RS.check_true,RS.seq_throw]
   rfl
 · rename_i accept
   have hfalse : (a.instruction_data.length != REQUEST_BYTES) = false := by
    cases h : (a.instruction_data.length != REQUEST_BYTES) <;> simp_all
   rw [hfalse,RS.check_false,RS.seq_pure]
   apply rsmember _ _ env _ _ (fromOption_member _ _ env)
   intro q
   split
   · rename_i reject
     change RS.seq (RS.check (NMX_R5_Request242.bad q) _) _ env _
     rw [reject,RS.check_true,RS.seq_throw]
     rfl
   · rename_i accept
     have hfalse : NMX_R5_Request242.bad q = false := by
      cases h : NMX_R5_Request242.bad q <;> simp_all
     change RS.seq (RS.check (NMX_R5_Request242.bad q) _) _ env _
     rw [hfalse,RS.check_false,RS.seq_pure]
     apply rsmember _ _ env _ _ (fromOption_member _ _ env)
     intro lane
     apply rsmember _ _ env _ _ rfl
     intro slot
     apply rsmember _ _ env _ _ rfl
     intro auth
     exact suffix_member q auth a.accounts env

#print axioms fromOption_member
#print axioms suffix_member
#print axioms replay_member
end NMX_R6_Port242
end
