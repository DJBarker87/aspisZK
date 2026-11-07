import PCM_Rejection
set_option autoImplicit false
namespace PCM
open RSL

def account0 : AccountInfo := ⟨zero32,zero32,false,false,false,0⟩
def identity0 : PoolIdentity := ⟨zero32,zero32,zero32,0,zero32⟩
def policy0 : VerifierPolicy := ⟨0,zero32,zero32,zero32⟩
def lane0 : LaneState := ⟨0,zero32,0,⟨0,[],List.replicate 20 []⟩⟩
def request0 : Request := ⟨zero32,zero32,zero32,.transfer ⟨zero32,zero32,0,[],[],0,[],[]⟩⟩
def result0 : TerminalResult := ⟨1,zero32,zero32,0,[],⟨0,[],List.replicate 20 []⟩⟩

theorem rejects_pure {A B : Type} (domain : A → Prop) (ref : A → Computation B)
    (a : A) (b : B) (wrong : ProgramError) (hd : domain a)
    (early : ref a = Computation.pure b) :
    ¬ PCM.RowSpec domain ref (fun _ s _ => ⟨.ret (.error wrong,s),[]⟩) := by
  intro h
  have hr := h a hd state0 env0
  rw [early] at hr
  have he := congrArg Observation.exit hr
  cases he
#print axioms rejects_pure
end PCM
