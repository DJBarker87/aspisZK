import AspisV8R19.SamplerWrapperPolicies

/-! Executable wrapper fixtures. Small byte-script helpers follow the pinned
R53 exporter; no random-oracle support is enumerated. Circle field inversion
is deliberately not represented as an executable word-refinement test. -/
set_option autoImplicit false
namespace AspisV8R19.WrapperReplay
open DuplexFrames SourceDuplexStep MemoizedProgramLaw SamplerWrapperPolicies

def octet (n : Nat) : Byte := ⟨n%256,Nat.mod_lt _ (by decide)⟩
def stateOf (n : Nat) : State := fun i => octet (n / 256^i.val)
def counter (input : Bytes) : Nat :=
  (input[0]?.getD 0).val + 256*(input[1]?.getD 0).val +
  65536*(input[2]?.getD 0).val + 16777216*(input[3]?.getD 0).val
def oracle (raw : List Nat) (frozen : Bool) (input : Bytes) : State :=
  if (input[32]?.getD 0).val = 1 then
    fun i => octet ((raw[8*counter input+i.val/4]?.getD 0) / 256^(i.val%4))
  else if (input[32]?.getD 0).val = 2 then stateOf (counter input + if frozen then 0 else 1)
  else stateOf 0
def csv (xs : List Nat) : String := String.intercalate "," (xs.map toString)
def outcome : Except Error (List Nat) → String
  | .ok xs => "ok:" ++ csv xs
  | .error .challengeExhausted => "err:challenge"
  | .error .subfieldExhausted => "err:subfield"
  | .error .parameterExhausted => "err:parameter"
def traceBytes (xs : List (Bytes × State)) : List Nat :=
  xs.flatMap (fun p => (p.1 ++ bytes p.2).map Fin.val)

def emit (out : IO.FS.Handle) (kind : String) (raw : List Nat)
    (frozen : Bool := false) : IO Unit := do
  let padded := (List.range 128).map (fun i => raw[i]?.getD 17 + if i%2=0 then 0 else 2147483648)
  let p := if kind = "n" then nonzeroProgram (stateOf 0) else oodProgram (stateOf 0)
  let r := eval (oracle padded frozen) p
  out.putStrLn (String.intercalate "|" [kind,toString (if frozen then 1 else 0 : Nat),
    csv padded,outcome r.2.1,csv ((bytes r.2.2).map Fin.val),csv (traceBytes r.1)])

def limbPrefix (count pattern : Nat) (value : List Nat) : List Nat :=
  (List.range count).flatMap (fun i =>
    List.replicate ((pattern / 8^i)%8) 2147483647 ++ [value[i]?.getD 0])
def paddedBlock (xs : List Nat) : List Nat :=
  xs ++ List.replicate ((8-xs.length%8)%8) 9
def candidate (pattern : Nat) (value : List Nat) := paddedBlock (limbPrefix 4 pattern value)
def rejected (attempts pattern : Nat) (value : List Nat) : List Nat :=
  (List.range attempts).flatMap (fun i => candidate (pattern+19*i) value)

def writeFixtures (path : System.FilePath) : IO Unit := do
  let out ← IO.FS.Handle.mk path .write
  for kind in ["n","o"] do
    let reject := if kind = "n" then [0,0,0,0] else [17,29,0,0]
    for before in List.range 3 do
      for pattern in List.range 16 do
        emit out kind (rejected before pattern reject ++ candidate (pattern+51) [17,29,43,71])
      for failedLimb in List.range 4 do
        for pattern in List.range 8 do
          emit out kind (rejected before pattern reject ++
            limbPrefix failedLimb pattern reject ++ List.replicate 8 2147483647)
    for pattern in List.range 32 do
      emit out kind (rejected 3 pattern reject)
    emit out kind [17,29,43,71,0,0,0,0] true
    emit out kind (reject ++ [0,0,0,0]) true
    emit out kind (List.replicate 8 2147483647) true
  out.flush
  IO.println "R54_WRAPPER_EXPORT rows=358 per_policy_success_schedules=48 per_policy_inner_failures=96 per_policy_outer_exhaustions=32 per_policy_frozen_controls=3 full_trace_bytes=true circle_word_refinement=false"
end AspisV8R19.WrapperReplay

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AspisV8R19.WrapperReplay.writeFixtures path
  | _ => throw (IO.userError "expected one NEW fixture-output path")
