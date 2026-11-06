import NKR_SumFinishData
import NJB_StateUpdates
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishPattern
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NKR_SumFinishData
abbrev State := Fin 26 → NQ
abbrev Scratch := Fin 103 → NQ

def scratchIndex (c : Fin 43) : Fin 103 := ⟨60+c.val,by have:=c.isLt;omega⟩
def step (scratch : Scratch) (lows : Fin 16 → NQ) (c : Fin 43) (before : State) : Result State :=
 NJB_StateUpdates.mulAdd before (pOut c) (scratch (scratchIndex c)) (lows (pLow c))

def modelStep (scratch : Fin 103 → K) (lows : Fin 16 → K) (c : Fin 43) (before : Fin 26 → K) : Fin 26 → K :=
 NJB_StateUpdates.addModel before (pOut c) (scratch (scratchIndex c)*lows (pLow c))

theorem source (scratch : Scratch) (lows : Fin 16 → NQ) (cs : List (Fin 43)) (before : State)
 (hs : ∀ i,Canon (scratch i)) (hl : ∀ i,Canon (lows i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (step scratch lows) cs before=ok after ∧
 (∀ i,Canon (after i)) ∧
 NJB_StateUpdates.decoded after=cs.foldl
 (fun state c=>modelStep (fun i=>decode (scratch i)) (fun i=>decode (lows i)) c state)
 (NJB_StateUpdates.decoded before) := by
 exact NJB_StateUpdates.run_result (step scratch lows)
  (modelStep (fun i=>decode (scratch i)) (fun i=>decode (lows i))) cs before hb
  (fun c _ state hc=>NJB_StateUpdates.mul_add_result state (pOut c)
   (scratch (scratchIndex c)) (lows (pLow c)) hc (hs _) (hl _))

#print axioms source
end AspisR1.NKR_SumFinishPattern
end
