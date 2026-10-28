import NDO_JFs_ExactInitialization
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_SeedBoundary
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def numeric : State := fun i => match i.val with
  | 0 => ⟨228,by omega⟩
  | 1 => ⟨169,by omega⟩
  | 2 => ⟨34,by omega⟩
  | 3 => ⟨97,by omega⟩
  | 4 => ⟨252,by omega⟩
  | 5 => ⟨244,by omega⟩
  | 6 => ⟨53,by omega⟩
  | 7 => ⟨226,by omega⟩
  | 8 => ⟨26,by omega⟩
  | 9 => ⟨140,by omega⟩
  | 10 => ⟨30,by omega⟩
  | 11 => ⟨138,by omega⟩
  | 12 => ⟨162,by omega⟩
  | 13 => ⟨243,by omega⟩
  | 14 => ⟨99,by omega⟩
  | 15 => ⟨242,by omega⟩
  | 16 => ⟨206,by omega⟩
  | 17 => ⟨9,by omega⟩
  | 18 => ⟨102,by omega⟩
  | 19 => ⟨152,by omega⟩
  | 20 => ⟨190,by omega⟩
  | 21 => ⟨134,by omega⟩
  | 22 => ⟨67,by omega⟩
  | 23 => ⟨110,by omega⟩
  | 24 => ⟨159,by omega⟩
  | 25 => ⟨218,by omega⟩
  | 26 => ⟨112,by omega⟩
  | 27 => ⟨61,by omega⟩
  | 28 => ⟨208,by omega⟩
  | 29 => ⟨157,by omega⟩
  | 30 => ⟨117,by omega⟩
  | 31 => ⟨30,by omega⟩
  | _ => ⟨0,by omega⟩

def zero : State := fun _ => ⟨0,by omega⟩

theorem numeric_ne_zero : numeric≠zero := by
  intro h
  have same := congrArg Fin.val (congrFun h ⟨0,by omega⟩)
  change 228=0 at same
  omega

/-- The installed digest body requires exactly this oracle realization; it
contains no concrete SHA256 compression body to evaluate. -/
theorem installed_iff (H : Bytes → State) (parts : SdkC_Source.Parts) (s : State) :
    MultiproofConePhysicalTransport.rawOracle H parts=encodeState s ↔ H (flatten parts)=s := by
  constructor
  · intro h
    have eq := congrArg decodeState h
    simpa only [MultiproofConePhysicalTransport.rawOracle,state_roundtrip] using eq
  · intro h
    exact congrArg encodeState h

theorem constant_zero_rejects_numeric (parts : SdkC_Source.Parts) :
    MultiproofConePhysicalTransport.rawOracle (fun _ => zero) parts≠encodeState numeric := by
  intro h
  have same := (installed_iff (fun _ => zero) parts numeric).mp h
  exact numeric_ne_zero same.symm

theorem no_universal_numeric (parts : SdkC_Source.Parts) :
    ¬∀ H : Bytes → State, MultiproofConePhysicalTransport.rawOracle H parts=encodeState numeric := by
  intro all
  exact constant_zero_rejects_numeric parts (all (fun _ => zero))

#print axioms numeric_ne_zero
#print axioms installed_iff
#print axioms constant_zero_rejects_numeric
#print axioms no_universal_numeric
end AspisR1.JFr_SeedBoundary
end
