import AspisV8R19.SamplerOracleLaws
import AspisV8R19.QM31SamplerInvariants

/-! Executable differential fixture exporter. It evaluates the proved causal
programs under a scripted FUNCTIONAL oracle. It does not enumerate random
oracles, prove a probability by testing, or execute a finite support set. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerReplay
open DuplexFrames SourceDuplexStep MemoizedProgramLaw OracleProgramOps

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
def fieldResult : Option (List Nat) → String
  | none => "err"
  | some xs => "ok:" ++ csv xs
def queryResult : Except Nat (List Nat) → String
  | .error n => "err:" ++ toString n
  | .ok xs => "ok:" ++ csv xs
def traceBytes (xs : List (Bytes × State)) : List Nat :=
  xs.flatMap (fun p => (p.1 ++ bytes p.2).map Fin.val)

def emit (out : IO.FS.Handle) (kind : String) (raw : List Nat) (frozen : Bool := false) : IO Unit := do
  let H := oracle raw frozen
  let (answer,state,trace) := if kind = "q" then
      let r := eval H (Q22SamplerProgram.challengeProgram (stateOf 0))
      (queryResult r.2.1,r.2.2,r.1)
    else if kind = "ff" then
      let p := bind (QM31SamplerProgram.challengeProgram (stateOf 0)) (fun first =>
        bind (QM31SamplerProgram.challengeProgram first.2) (fun second =>
          .done ((first.1,second.1),second.2)))
      let r := eval H p
      (fieldResult r.2.1.1 ++ "/" ++ fieldResult r.2.1.2,r.2.2,r.1)
    else
      let r := eval H (QM31SamplerProgram.challengeProgram (stateOf 0))
      (fieldResult r.2.1,r.2.2,r.1)
  out.putStrLn (String.intercalate "|" [kind,toString (if frozen then 1 else 0 : Nat),
    csv raw,answer,csv ((bytes state).map Fin.val),csv (traceBytes trace)])

def limbPrefix (count pattern : Nat) : List Nat :=
  (List.range count).flatMap (fun i =>
    List.replicate ((pattern / 8^i)%8) 2147483647 ++ [17*pattern+19*i])
def paddedHigh (seed : Nat) (xs : List Nat) : List Nat :=
  (List.range 72).map (fun i =>
    xs[i]?.getD (100000+i) + if (i+seed)%2=0 then 0 else 2147483648)

def writeFixtures (path : System.FilePath) : IO Unit := do
  let out ← IO.FS.Handle.mk path .write
  for pattern in List.range 4096 do
    emit out "f" (paddedHigh pattern (limbPrefix 4 pattern))
  for failedLimb in List.range 4 do
    for pattern in List.range (8^failedLimb) do
      emit out "f" (paddedHigh pattern (limbPrefix failedLimb pattern ++ List.replicate 8 2147483647))
  for shift in List.range 43 do
    let hit := 22+shift
    let raw := (List.range 72).map (fun i =>
      (if i<21 then i else if i=hit-1 then 21 else 0) + (((i+hit)%16384)*262144))
    emit out "q" raw
  for distinct in (List.range 21).map (·+1) do
    emit out "q" ((List.range 72).map (fun i => i%distinct))
  emit out "f" (List.range 72) true
  emit out "f" (List.replicate 7 2147483647 ++ [42] ++ List.replicate 64 0) true
  emit out "f" (List.replicate 72 2147483647) true
  emit out "q" (List.range 72) true
  emit out "ff" (List.range 72)
  emit out "ff" (paddedHigh 1 (limbPrefix 4 4095))
  emit out "ff" (List.replicate 8 2147483647 ++ List.range 64)
  emit out "ff" (List.replicate 72 2147483647)
  out.flush
  IO.println "R53_MODEL_EXPORT field_success_schedules=4096 field_failure_schedules=585 query_cases=64 frozen_cases=4 sequential_calls=4 rows=4753 full_trace_bytes=true"
end AspisV8R19.SamplerReplay

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AspisV8R19.SamplerReplay.writeFixtures path
  | _ => throw (IO.userError "expected one NEW fixture-output path")
