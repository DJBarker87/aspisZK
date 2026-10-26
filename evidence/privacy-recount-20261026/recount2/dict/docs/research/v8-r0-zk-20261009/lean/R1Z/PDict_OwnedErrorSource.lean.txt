import R1Z.PDict_ErrorKind
set_option autoImplicit false
namespace PDict_OwnedErrorSource
open Aeneas Aeneas.Std Result
/-- Same42constructors as the baseline reference emission; associated with
its already-extracted core ErrorKind, not with dynamic std.io.Error. -/
abbrev core.io.error.ErrorKind := ProverRwFull.core.io.error.ErrorKind
structure owned_error.OwnedError where
  kind : core.io.error.ErrorKind

/-- [pdict_offpath::owned_error::Observation]
    Source: '../proof-std-native/owned_error.rs', lines 7:0-7:80
    Visibility: public -/
structure owned_error.Observation where
  reserved : Bool
  last_error : Option core.io.error.ErrorKind


/-- [core::io::error::{impl core::cmp::PartialEq<core::io::error::ErrorKind> for core::io::error::ErrorKind}::eq]:
    Source: '/rustc/library/core/src/io/error.rs', lines 40:44-40:53
    Name pattern: [core::io::error::{core::cmp::PartialEq<core::io::error::ErrorKind, core::io::error::ErrorKind>}::eq]
    Visibility: public -/
@[rust_fun
  "core::io::error::{core::cmp::PartialEq<core::io::error::ErrorKind, core::io::error::ErrorKind>}::eq"]
def core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq
  (self : core.io.error.ErrorKind) (other : core.io.error.ErrorKind) :
  Result Bool
  := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [pdict_offpath::owned_error::owned_observe]:
    Source: '../proof-std-native/owned_error.rs', lines 8:0-13:1
    Visibility: public -/
def owned_error.owned_observe
  (result : core.result.Result Bool owned_error.OwnedError) :
  Result owned_error.Observation
  := do
  match result with
  | core.result.Result.Ok reserved => ok { reserved, last_error := none }
  | core.result.Result.Err error =>
    ok { reserved := false, last_error := (some error.kind) }

/-- [pdict_offpath::owned_error::owned_open_error]:
    Source: '../proof-std-native/owned_error.rs', lines 20:0-22:1
    Visibility: public -/
def owned_error.owned_open_error
  (error : owned_error.OwnedError) :
  Result (core.result.Result Bool owned_error.OwnedError)
  := do
  let b ←
    core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq error.kind
      ProverRwFull.core.io.error.ErrorKind.AlreadyExists
  if b
  then ok (core.result.Result.Ok false)
  else ok (core.result.Result.Err error)

/-- [pdict_offpath::owned_error_observe]:
    Source: 'lib.rs', lines 78:0-80:1
    Visibility: public -/
def owned_error_observe
  (r : core.result.Result Bool owned_error.OwnedError) :
  Result owned_error.Observation
  := do
  owned_error.owned_observe r

/-- [pdict_offpath::owned_error_open]:
    Source: 'lib.rs', lines 82:0-84:1
    Visibility: public -/
def owned_error_open
  (e : owned_error.OwnedError) :
  Result (core.result.Result Bool owned_error.OwnedError)
  := do
  owned_error.owned_open_error e


#print axioms core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq
#print axioms owned_error.owned_observe
#print axioms owned_error.owned_open_error
#print axioms owned_error_observe
#print axioms owned_error_open
end PDict_OwnedErrorSource
