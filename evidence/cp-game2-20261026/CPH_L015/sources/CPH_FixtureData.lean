import CPH_Game
import CPR_AdmissionGap
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureData
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store

def byte (n : Nat) : U8 := U8.ofNat (n % 256) (by have := Nat.mod_lt n (by decide : 0 < 256); omega)
def key (n : Nat) : S2W_ExtractionBoundary.Program := Hist_Nonvacuity.key (byte n)
def id : S2W_ExtractionBoundary.Program := Hist_Nonvacuity.key 255#u8

def zeros (n : Nat) (bound : n < 65536) : Slice U8 :=
  ⟨List.replicate n (0#u8),by simp only [List.length_replicate]; scalar_tac⟩
def buffer : Nat → Slice U8
  | 0 => zeros 58295 (by decide)
  | 1 => zeros 1880 (by decide)
  | 2 => zeros 1768 (by decide)
  | 3 => zeros 384 (by decide)
  | 4 => zeros 192 (by decide)
  | 5 => zeros 768 (by decide)
  | 6 => zeros 128 (by decide)
  | _ => zeros 192 (by decide)

def record (n : Nat) : Record :=
  ⟨⟨key n,id,false,decide (n=2),false,.Ok 0#usize,.Ok ⟨[],by simp⟩⟩,1,0⟩
def readerCell (n : Nat) : Nat := if n = 0 then 0 else if n = 6 then 2 else n+2
def layout1 : Layout := ⟨fun n => (n,n+100),record,fun n => n*65536,fun n => n⟩
def layout2 : Layout := ⟨fun n => (readerCell n,readerCell n+100),record,fun n => n*65536,fun n => n⟩
def initial : Bank := ⟨fun n => ⟨id,buffer n⟩,fun _ => 1⟩
def saved : alloc.vec.Vec U8 := ⟨Hist_Nonvacuity.checkpoint.val,Hist_Nonvacuity.checkpoint.property⟩
def allocator : Allocator Unit := ⟨fun _ _ => ok (),fun _ => ok ()⟩
/-- Deliberately local wrapper witnesses. No DrvC source extraction is asserted. -/
def n1 : S2W_ExtractionBoundary.First := fun _ _ _ => ok (.Ok saved)
def n2 : S2W_ExtractionBoundary.Second := fun _ _ _ _ => ok (.Ok ())
def copy := S2W_TrustedStd.specification (F := Nat → Record)
def suffix : List (Action Unit) := [.credit 2 5,.reap 2,.rollback]
def final : Bank :=
  (CPP_BankHistory.run n1 n2 copy allocator id
    (CPR_SourceBank.afterCopy (cached initial) 2 saved) suffix).1

def observations : Observations Bool Unit where
  bank := fun t => if t then final else initial
  layout := fun t => if t then layout2 else layout1
  next := fun t u => t = false ∧ u = true
  intervening := fun _ _ => []
  parentReply := fun _ => .ok (.Ok ())
  copied := fun _ => saved
  actions := fun _ => suffix
  parentTentative := fun t =>
    (CPP_BankHistory.run n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy (cached (if t then final else initial))
        ((if t then layout2 else layout1).handles 2).1 saved) suffix).1
  physicalEvents := fun t =>
    (CPP_BankHistory.run n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy (cached (if t then final else initial))
        ((if t then layout2 else layout1).handles 2).1 saved) suffix).2

def e1 : Entry := entry observations false
def e2 : Entry := entry observations true
end AspisR1.CPH_FixtureData
end
