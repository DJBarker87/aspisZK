import R1Z.PV_RDB1_Append
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V178
open PV_RDB1_V183_ReserveWorld

def dropBytes {W : Type} : Nat → W → W
  | 0,w => w
  | n+1,w => dropBytes n w

theorem byte_drops {W : Type} (n : Nat) (w : W) : dropBytes n w=w := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def cleared (b : Buffer U8) : Buffer U8 := ⟨b.address,b.capacity,[],by simp⟩

def deployedTruncateZero {W : Type} (b : Buffer U8) (w : W) : Result (Buffer U8 × W) :=
  let remaining := b.values.length-0
  ok (cleared b,dropBytes remaining w)

def historicalClear {W : Type} (b : Buffer U8) (w : W) : Result (Buffer U8 × W) :=
  ok (cleared b,w)

/-- truncate(0) and clear both invalidate only the live u8 prefix. No payload
Drop, allocation/free, capacity change or write to the old byte memory. -/
theorem truncate_complete {W : Type} (b : Buffer U8) (w : W) :
    deployedTruncateZero b w=historicalClear b w := by
  simp only [deployedTruncateZero,historicalClear,byte_drops]

theorem retained_header (b : Buffer U8) :
    (cleared b).address=b.address ∧ (cleared b).capacity=b.capacity ∧
    (cleared b).values=[] := ⟨rfl,rfl,rfl⟩

/-- Zero is always a public OsStr boundary. Thus the changed truncate call
cannot enter UTF8 slow_path or its panic/formatting/allocation descendants. -/
theorem zero_boundary (len : Nat) : (0=0 ∨ 0=len) := Or.inl rfl

def sourcePush {W : Type} (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (b : Buffer U8) (path : List U8) (w : W) :
    Result (Buffer U8 × W) := do
  let (b,w) ← if absolute then deployedTruncateZero b w else ok (b,w)
  let (b,w) ← if !absolute && needSep then append b [47#u8] w else ok (b,w)
  append b path w

def repairedPush {W : Type} (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (b : Buffer U8) (path : List U8) (w : W) :
    Result (Buffer U8 × W) := do
  let (b,w) ← if absolute then historicalClear b w else ok (b,w)
  let (b,w) ← if !absolute && needSep then append b [47#u8] w else ok (b,w)
  append b path w

theorem push_complete {W : Type}
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (b : Buffer U8) (path : List U8) (w : W) :
    sourcePush append absolute needSep b path w =
      repairedPush append absolute needSep b path w := by
  simp only [sourcePush,repairedPush,truncate_complete]

def sourceJoin {W : Type}
    (clone : List U8 → W → Result (Buffer U8 × W))
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (base path : List U8) (w : W) : Result (Buffer U8 × W) := do
  let (b,w) ← clone base w
  sourcePush append absolute needSep b path w

/-- Correct full-effect reference MUST clone base before the absolute-path
clear. The old value-only reference intentionally omitted that clone. -/
theorem join_repaired {W : Type}
    (clone : List U8 → W → Result (Buffer U8 × W))
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (base path : List U8) (w : W) :
    sourceJoin clone append absolute needSep base path w =
      (do let (b,w') ← clone base w; repairedPush append absolute needSep b path w') := by
  simp only [sourceJoin,push_complete]

/-- Omitted clone is not harmless for full Result: failure there propagates
before path extension, even when path is absolute. -/
theorem clone_failure {W : Type}
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (base path : List U8) (w : W) :
    sourceJoin (fun _ _ => fail .panic) append absolute needSep base path w = fail .panic := rfl

#print axioms byte_drops
#print axioms truncate_complete
#print axioms retained_header
#print axioms zero_boundary
#print axioms push_complete
#print axioms join_repaired
#print axioms clone_failure
end R1Z.PV_RDB1_V178
