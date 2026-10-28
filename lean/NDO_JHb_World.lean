import JHb_Programs
import NDO_JHb_Header
import JHb_DataMaster
import JHb_DataForest
import JHb_DataLane
import JHb_DataRegistry
import JHb_DataEntry
import NDO_JFv_World
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_World
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry

def buffer : Nat → Slice U8
  | 0 => JHb_Header.account
  | 1 => JFx_NativeBytes.publicInput
  | 3 => JHb_DataMaster.value
  | 4 => JHb_DataForest.value
  | 5 => JHb_DataLane.value
  | 6 => JHb_DataRegistry.value
  | 7 => JHb_DataEntry.value
  | n => CPH_FixtureData.buffer n

def owner : Nat → S2W_ExtractionBoundary.Program
  | 0 | 1 => JHb_Programs.foreign
  | 3 | 4 | 5 => JHb_Programs.pool
  | 6 | 7 => JHb_Programs.registry
  | _ => CPH_Program.verifier

def initial : Bank := ⟨fun n => ⟨owner n,buffer n⟩,fun _ => 1⟩
def final : Bank := CPR_SourceBank.afterCopy (cached initial) 2 JFv_World.saved
/-- Constructed default-configuration runtime tuple. Fixed measurement hashes
in V2 records are fixture data, not certificates of a loaded executable. -/
def observations : Observations Bool Unit where
  bank := fun t => if t then final else initial
  layout := fun t => if t then CPH_FixtureData.layout2 else CPH_FixtureData.layout1
  next := fun t u => t=false ∧ u=true
  intervening := fun _ _ => []
  parentReply := fun _ => .ok (.Ok ())
  copied := fun _ => JFv_World.saved
  actions := fun _ => []
  parentTentative := fun t => if t then cached final else final
  physicalEvents := fun _ => []
def e1 := entry observations false
def e2 := entry observations true
end AspisR1.JHb_World
end
