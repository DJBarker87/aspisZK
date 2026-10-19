import CuSavingsRhoBasis
import CuSavingsRhoZipInitialization

/-! Consume actual emitted basis results to discharge the batch admission
conditions. Only canonical query power, bounded length and source-produced
basis executions remain; no abstract valid-index/basis premise is exposed.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoBasisPipeline
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoPushStep CuSavingsRhoBatches

structure Input where
  power : field.QM31
  node : U32

def prepare (length : Usize) (hlen : length.val ≤ 256) (input : Input) :
    Result CuSavingsRhoBatches.Input := do
  let basis ← AspisR1RhoBasis.basis length input.node
  .ok {power:=input.power,items:=CuSavingsRhoInputs.items basis length hlen}

theorem prepare_admitted (length : Usize) (hlen : length.val ≤ 256)
    (input : Input) (out : CuSavingsRhoBatches.Input) (hp : Canonical input.power)
    (h : prepare length hlen input = .ok out) : Admitted out length.val := by
  unfold prepare at h
  cases hb : AspisR1RhoBasis.basis length input.node with
  | fail error => simp only [hb,bind_tc_fail] at h;cases h
  | div => simp only [hb,bind_tc_div] at h;cases h
  | ok basis =>
    simp only [hb,bind_tc_ok] at h
    cases Result.ok.inj h
    exact CuSavingsRhoBasis.input_admitted length input.node basis input.power hlen hp hb

def inputs (length : Usize) (hlen : length.val ≤ 256) (raw : List (Result Input)) :
    List (Result CuSavingsRhoBatches.Input) := raw.map (fun r => do
  let input ← r
  prepare length hlen input)

theorem inputs_admitted (length : Usize) (hlen : length.val ≤ 256)
    (raw : List (Result Input))
    (hp : ∀ input,Result.ok input ∈ raw → Canonical input.power) :
    ∀ data,Result.ok data ∈ inputs length hlen raw → Admitted data length.val := by
  intro data hm
  obtain ⟨result,hmem,heq⟩ := List.mem_map.mp hm
  cases result with
  | fail error => cases heq
  | div => cases heq
  | ok input => exact prepare_admitted length hlen input data (hp input hmem) heq

theorem pipeline_eq (raw : Slice Raw4) (weights : Slice field.QM31)
    (length : Usize) (hlen : length.val ≤ 256) (hweights : weights.val.length = length.val)
    (requests : List (Result Input))
    (hraw : raw.val.length = weights.val.length)
    (hc : ∀ weight ∈ weights.val,Canonical weight)
    (hcount : requests.length ≤ 22)
    (hp : ∀ input,Result.ok input ∈ requests → Canonical input.power) :
    (do let state ← CuSavingsRhoZipInitialization.construct raw weights
        optimized (inputs length hlen requests) state weights) =
      reference (inputs length hlen requests) weights := by
  apply CuSavingsRhoZipInitialization.pipeline_eq raw weights _ hraw hc
  · simpa only [inputs,List.length_map] using hcount
  · intro data hd
    rw [hweights]
    exact inputs_admitted length hlen requests hp data hd

#print axioms prepare_admitted
#print axioms inputs_admitted
#print axioms pipeline_eq
end AspisR1.CuSavingsRhoBasisPipeline
