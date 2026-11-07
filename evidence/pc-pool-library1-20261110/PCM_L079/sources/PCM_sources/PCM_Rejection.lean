import PCM_Carriers
import PCM_Algebra
set_option autoImplicit false
namespace PCM
open RSL

def state0 : State :=
  { sdk := ⟨fun _ => ⟨[],[],none⟩,0⟩
    lamportSdk := ⟨fun _ => ⟨[],[],none⟩,0⟩
    lamportCell := id
    lamports := fun _ => 0
    owners := fun _ => zero32
    returnData := none
    callIndex := 0 }
def rent0 : PCM.Rent := ⟨0,0,0⟩

/-- Exact early-error witness, with a fixed inhabited state and environment. -/
theorem rejects_error {A B : Type} (domain : A → Prop) (ref : A → Computation B)
    (a : A) (e wrong : ProgramError) (hd : domain a)
    (early : ref a = Computation.throw e) (different : wrong ≠ e) :
    ¬ PCM.RowSpec domain ref (fun _ s _ => ⟨.ret (.error wrong,s),[]⟩) := by
  intro h
  have hr := h a hd state0 env0
  rw [early] at hr
  have he : wrong = e := by
    have hx : (Except.error wrong : Except ProgramError B) = .error e :=
      congrArg Prod.fst (RSL.Exit.ret.inj (congrArg Observation.exit hr))
    exact Except.error.inj hx
  exact different he

#print axioms rejects_error
end PCM
