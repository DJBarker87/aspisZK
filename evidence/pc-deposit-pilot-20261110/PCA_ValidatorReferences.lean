import PCA_ProgramIds
import PCA_Event
set_option autoImplicit false
namespace PCA

def supportedLoader (owner : Bytes) : Bool :=
  owner == bpf_loader || owner == bpf_loader_upgradeable || owner == loader_v4

def tokenProgramReference (account : Nat) (s : PCA_State) : Execution Unit :=
  let a := s.loans.state.accounts account
  let valid := a.key == token_program && a.executable && !a.signer && !a.writable && supportedLoader a.owner
  ⟨s,[],if valid then .ok () else .error (.program 0x41532013)⟩

def payerSystemReference (args : Nat × Nat) (s : PCA_State) : Execution Unit :=
  let payer := s.loans.state.accounts args.1
  let system := s.loans.state.accounts args.2
  let payerValid := payer.signer && payer.writable && !payer.executable && payer.owner == system_program
  let systemValid := system.key == system_program && system.owner == native_loader &&
    system.executable && !system.signer && !system.writable
  ⟨s,[],if !payerValid then .error (.program 0x41532034)
    else if !systemValid then .error (.program 0x41532033) else .ok ()⟩

def uniqueReference (_ : Unit) (s : PCA_State) : Execution Unit :=
  let keys := (List.range s.accountCount).map (fun a => (s.loans.state.accounts a).key)
  ⟨s,[],if keys.Pairwise (· ≠ ·) then .ok () else .error (.program (2 * 2^32))⟩

end PCA
