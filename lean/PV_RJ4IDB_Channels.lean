import PV_DIAG2_Effects
import PV_DIAG3_Execution
/-! Lossless observation alphabet. File operations include failed/partial requests;
wall-time is its exact serialized representation, not rounded/zeroed time.
Query/rejection prefixes and every retained side channel remain ordered. -/
set_option autoImplicit false
namespace PV_RJ4IDB
abbrev Bytes := List UInt8
inductive FileOp where
 | create (path : Bytes) (mode : Nat)
 | write (path requested delivered : Bytes)
 | sync (path : Bytes)
 | failed (path message : Bytes)
 deriving Repr
inductive Event where
 | file (op : FileOp)
 | returnedJson (json : Bytes)
 | stdout (requested delivered : Bytes)
 | diagnostic2 (effect : PV_DIAG2.Effect)
 | diagnostic3 (effect : PV_DIAG3.Event)
 | attempts (count : Nat)
 | proveWallSeconds (serialized : Bytes)
 | query (address answer : Bytes)
 | rejected (attempt : Nat)
 | retained (channel payload : Bytes)
 deriving Repr
inductive Terminal (A : Type) where
 | success (value : A)
 | failure (error : Bytes)
 | panic (value : PV_DIAG3.Panic)
 | abort (value : PV_DIAG3.Crash)
 | diverge
 deriving Repr
structure Trace (A : Type) where
 events : List Event
 terminal : Terminal A
 deriving Repr
/-- Each divergent execution is represented by ALL its finite prefixes, not
one fixed empty prefix. The same carrier also includes every failure prefix. -/
abbrev PrefixFamily (I A : Type) := I → Trace A

def files : List Event → List FileOp := List.filterMap fun e =>
 match e with | .file op => some op | _ => none

def json : List Event → List Bytes := List.filterMap fun e =>
 match e with | .returnedJson b => some b | _ => none

def stdout : List Event → List (Bytes × Bytes) := List.filterMap fun e =>
 match e with | .stdout a b => some (a,b) | _ => none

def diagnostics2 : List Event → List PV_DIAG2.Effect := List.filterMap fun e =>
 match e with | .diagnostic2 a => some a | _ => none

def diagnostics3 : List Event → List PV_DIAG3.Event := List.filterMap fun e =>
 match e with | .diagnostic3 a => some a | _ => none

def counts : List Event → List Nat := List.filterMap fun e =>
 match e with | .attempts n => some n | _ => none

def times : List Event → List Bytes := List.filterMap fun e =>
 match e with | .proveWallSeconds b => some b | _ => none

def oracle : List Event → List (Bytes × Bytes) := List.filterMap fun e =>
 match e with | .query a b => some (a,b) | _ => none

def rejections : List Event → List Nat := List.filterMap fun e =>
 match e with | .rejected n => some n | _ => none

def sideChannels : List Event → List (Bytes × Bytes) := List.filterMap fun e =>
 match e with | .retained a b => some (a,b) | _ => none

theorem files_append (a b : List Event) : files (a++b) = files a ++ files b :=
 List.filterMap_append
#print axioms files_append
end PV_RJ4IDB
