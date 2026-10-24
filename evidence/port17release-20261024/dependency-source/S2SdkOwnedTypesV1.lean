-- Exact generated owned state declarations; protocol types are reused below.
import S2OwnedStage1TypesV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisS2OwnedStage1.SdkReference

/-- [aspis_s126_owned_sdk::SolanaDigest]
    Source: 'src/lib.rs', lines 5:22-5:42 -/
@[reducible]
def SolanaDigest := Unit

/-- [aspis_s126_owned_sdk::decode_public_statement_box::closure]
    Source: 'src/lib.rs', lines 20:21-20:57 -/
@[reducible]
def decode_public_statement_box.closure := Unit

/-- [aspis_s126_owned_sdk::OwnedAccount]
    Source: 'src/lib.rs', lines 25:0-28:1
    Visibility: public -/
structure OwnedAccount where
  key : Array Std.U8 32#usize
  owner : Array Std.U8 32#usize
  is_signer : Bool
  is_writable : Bool
  executable : Bool
  rent_epoch : Std.U64
  data_slot : Std.Usize
  lamports_slot : Std.Usize

/-- [aspis_s126_owned_sdk::OwnedDataCell]
    Source: 'src/lib.rs', lines 29:0-31:1
    Visibility: public -/
structure OwnedDataCell where
  bytes : alloc.vec.Vec Std.U8
  borrowed : Std.Isize
  strong : Std.Usize
  weak : Std.Usize

/-- [aspis_s126_owned_sdk::OwnedLamportsCell]
    Source: 'src/lib.rs', lines 32:0-34:1
    Visibility: public -/
structure OwnedLamportsCell where
  amount : Std.U64
  borrowed : Std.Isize
  strong : Std.Usize
  weak : Std.Usize

/-- [aspis_s126_owned_sdk::OwnedSdk]
    Source: 'src/lib.rs', lines 35:0-38:1
    Visibility: public -/
structure OwnedSdk where
  accounts : alloc.vec.Vec OwnedAccount
  data_cells : alloc.vec.Vec OwnedDataCell
  lamports_cells : alloc.vec.Vec OwnedLamportsCell

/-- [aspis_s126_owned_sdk::LiveGuards]
    Source: 'src/lib.rs', lines 39:0-41:1
    Visibility: public -/
structure LiveGuards where
  checkpoint : Option Std.Usize
  «public» : Option Std.Usize
  proof : Option Std.Usize

/-- [aspis_s126_owned_sdk::owned_stage1_body::closure#1]
    Source: 'src/lib.rs', lines 98:11-98:46 -/
@[reducible]
def owned_stage1_body.closure_1 := Unit

/-- [aspis_s126_owned_sdk::owned_stage1_body::closure]
    Source: 'src/lib.rs', lines 96:72-96:107 -/
@[reducible]
def owned_stage1_body.closure := Unit

end AspisS2OwnedStage1.SdkReference

#print axioms AspisS2OwnedStage1.SdkReference.OwnedSdk
