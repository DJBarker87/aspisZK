import R1Z.PV_RDB1_V178
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEA_V178
open PV_RDB1_V183_ReserveWorld
/-- AsRef is evaluated first; clone, truncate/separator, append follow. The
consumer receives the entire Result, including failures and the returned world. -/
def adapter {P W R : Type} (asRef : P → Result (List U8))
    (clone : List U8 → W → Result (Buffer U8 × W))
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (base : List U8) (arg : P) (w : W)
    (consume : Result (Buffer U8 × W) → R) : R :=
  consume (do
    let path ← asRef arg
    PV_RDB1_V178.sourceJoin clone append absolute needSep base path w)

theorem consumer {P W R : Type} (asRef : P → Result (List U8))
    (clone : List U8 → W → Result (Buffer U8 × W))
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (base : List U8) (arg : P) (w : W)
    (consume : Result (Buffer U8 × W) → R) :
    adapter asRef clone append absolute needSep base arg w consume =
    consume (do
      let path ← asRef arg
      let (b,w') ← clone base w
      PV_RDB1_V178.repairedPush append absolute needSep b path w') := by
  unfold adapter
  congr 1
  cases h : asRef arg <;> simp only [bind_tc_ok,bind_tc_fail]
  simp only [PV_RDB1_V178.join_repaired]

/-- A value-only successful consumer cannot represent clone failure, including
on absolute paths; no allocation-success hypothesis is introduced. -/
theorem clone_rejection {W : Type}
    (append : Buffer U8 → List U8 → W → Result (Buffer U8 × W))
    (absolute needSep : Bool) (base path : List U8) (w : W)
    (returned : Buffer U8 × W) :
    PV_RDB1_V178.sourceJoin (fun _ _ => fail .panic) append
      absolute needSep base path w ≠ ok returned := by
  rw [PV_RDB1_V178.clone_failure]
  intro h
  cases h

#print axioms consumer
#print axioms clone_rejection
end R1Z.PV_RDEA_V178
