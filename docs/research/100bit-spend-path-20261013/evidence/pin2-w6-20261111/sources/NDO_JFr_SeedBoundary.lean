import NDO_JFs_ExactInitialization
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_SeedBoundary
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def numeric : State := fun i => match i.val with
  | 0 => ⟨23,by omega⟩
  | 1 => ⟨102,by omega⟩
  | 2 => ⟨121,by omega⟩
  | 3 => ⟨105,by omega⟩
  | 4 => ⟨55,by omega⟩
  | 5 => ⟨42,by omega⟩
  | 6 => ⟨33,by omega⟩
  | 7 => ⟨197,by omega⟩
  | 8 => ⟨131,by omega⟩
  | 9 => ⟨49,by omega⟩
  | 10 => ⟨54,by omega⟩
  | 11 => ⟨191,by omega⟩
  | 12 => ⟨148,by omega⟩
  | 13 => ⟨78,by omega⟩
  | 14 => ⟨140,by omega⟩
  | 15 => ⟨199,by omega⟩
  | 16 => ⟨251,by omega⟩
  | 17 => ⟨10,by omega⟩
  | 18 => ⟨176,by omega⟩
  | 19 => ⟨229,by omega⟩
  | 20 => ⟨62,by omega⟩
  | 21 => ⟨164,by omega⟩
  | 22 => ⟨10,by omega⟩
  | 23 => ⟨207,by omega⟩
  | 24 => ⟨236,by omega⟩
  | 25 => ⟨102,by omega⟩
  | 26 => ⟨202,by omega⟩
  | 27 => ⟨10,by omega⟩
  | 28 => ⟨253,by omega⟩
  | 29 => ⟨208,by omega⟩
  | 30 => ⟨80,by omega⟩
  | 31 => ⟨161,by omega⟩
  | _ => ⟨0,by omega⟩

def zero : State := fun _ => ⟨0,by omega⟩

theorem numeric_ne_zero : numeric≠zero := by
  intro h
  have same := congrArg Fin.val (congrFun h ⟨0,by omega⟩)
  change 23=0 at same
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
