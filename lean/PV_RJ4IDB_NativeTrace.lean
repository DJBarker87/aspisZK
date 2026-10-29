import PV_RJ4IDB_Decoder
/-! Native channel records, with separate file and terminal constructors.
These are observations of native executions; producing the records from the
deployed program is owned by runjoin/diag/L1 as recorded in OPEN-INPUTS.md. -/
set_option autoImplicit false
namespace PV_RJ4IDB
inductive NativeEvent where
 | proofWrite (path requested delivered : Bytes)
 | statementWrite (path requested delivered : Bytes)
 | otherFile (op : FileOp)
 | returned (json : Bytes)
 | printed (requested delivered : Bytes)
 | diag2 (effect : PV_DIAG2.Effect)
 | diag3 (effect : PV_DIAG3.Event)
 | count (attempts : Nat)
 | wall (serializedSeconds : Bytes)
 | oracle (address answer : Bytes)
 | rejection (attempt : Nat)
 | side (name payload : Bytes)
 deriving Repr

def translateEvent : NativeEvent → Event
 | .proofWrite p a b => .file (.write p a b)
 | .statementWrite p a b => .file (.write p a b)
 | .otherFile f => .file f
 | .returned j => .returnedJson j
 | .printed a b => .stdout a b
 | .diag2 e => .diagnostic2 e
 | .diag3 e => .diagnostic3 e
 | .count n => .attempts n
 | .wall b => .proveWallSeconds b
 | .oracle a b => .query a b
 | .rejection n => .rejected n
 | .side a b => .retained a b

structure NativeTrace (A : Type) where
 events : List NativeEvent
 terminal : Terminal A

def modelTrace {A : Type} (t : NativeTrace A) : Trace A :=
 ⟨t.events.map translateEvent,t.terminal⟩

def nativeFiles : List NativeEvent → List FileOp := List.filterMap fun e =>
 match e with
 | .proofWrite p a b => some (.write p a b)
 | .statementWrite p a b => some (.write p a b)
 | .otherFile f => some f
 | _ => none

def nativeJSON : List NativeEvent → List Bytes := List.filterMap fun e =>
 match e with | .returned j => some j | _ => none

def nativeStdout : List NativeEvent → List (Bytes × Bytes) := List.filterMap fun e =>
 match e with | .printed a b => some (a,b) | _ => none

def nativeDiag2 : List NativeEvent → List PV_DIAG2.Effect := List.filterMap fun e =>
 match e with | .diag2 a => some a | _ => none

def nativeDiag3 : List NativeEvent → List PV_DIAG3.Event := List.filterMap fun e =>
 match e with | .diag3 a => some a | _ => none

def nativeCounts : List NativeEvent → List Nat := List.filterMap fun e =>
 match e with | .count n => some n | _ => none

def nativeTimes : List NativeEvent → List Bytes := List.filterMap fun e =>
 match e with | .wall b => some b | _ => none

def nativeOracle : List NativeEvent → List (Bytes × Bytes) := List.filterMap fun e =>
 match e with | .oracle a b => some (a,b) | _ => none

def nativeRejections : List NativeEvent → List Nat := List.filterMap fun e =>
 match e with | .rejection n => some n | _ => none

def nativeSide : List NativeEvent → List (Bytes × Bytes) := List.filterMap fun e =>
 match e with | .side a b => some (a,b) | _ => none
end PV_RJ4IDB
