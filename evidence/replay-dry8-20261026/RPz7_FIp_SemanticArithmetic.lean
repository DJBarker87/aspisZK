import ExtractedMaskCallerModel
import RPz7_FIo_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_SemanticArithmetic
open Aeneas Aeneas.Std Result
abbrev MQ := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31
abbrev B := AspisR1PublicPreparation.FinishModel.Boundaries

def toProbe (x : MQ) : PQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromProbe (x : PQ) : MQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def mapResult : Result PQ → Result MQ
  | .ok x => .ok (fromProbe x) | .fail e => .fail e | .div => .div

def mapArray {N : Usize} (a : Array MQ N) : Array PQ N :=
  ⟨a.val.map toProbe,by simpa only [List.length_map] using a.property⟩

def add (x y : MQ) : Result MQ := mapResult (AspisR1SelectedMaskProbe.field.QM31.add (toProbe x) (toProbe y))
def mul (x y : MQ) : Result MQ := mapResult (AspisR1SelectedMaskProbe.field.QM31.mul (toProbe x) (toProbe y))
def mask (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize) : Result MQ :=
  mapResult (AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
    (mapArray c1) (mapArray m) (toProbe g) (mapArray point))

def install (seed : B) : B := {seed with mask:=mask,add:=add,mul:=mul}

theorem roundtrip (x : MQ) : fromProbe (toProbe x)=x := rfl

theorem slots (seed : B) :
    (install seed).mask=mask ∧ (install seed).add=add ∧ (install seed).mul=mul ∧
    (install seed).terminal=seed.terminal := ⟨rfl,rfl,rfl,rfl⟩

#print axioms roundtrip
#print axioms slots
end AspisR1.FIp_SemanticArithmetic
end
