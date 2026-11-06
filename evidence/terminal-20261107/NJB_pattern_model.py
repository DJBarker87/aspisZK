from pathlib import Path
import json
E=Path(__file__).resolve().parent;t=json.loads((E/'NJB_PATTERN_TABLE.json').read_text())['tables'];p=t['COPY_PATTERN_COORDINATE_PATTERNS'];off=t['COPY_PATTERN_GROUP_OFFSETS'];assert len(p)==26 and len(off)==5 and all(0<=x<14 for x in p) and off==[0,9,12,21,26]
s='''import NJB_StateUpdates
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_PatternReference
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJB_StateUpdates (canonical decoded addModel)
abbrev State := Fin 4 → NQ
/-- Exact frozen pattern-coordinate and group tables, not free coefficients. -/
def pattern : Fin 26 → Fin 14 := !['''+','.join(map(str,p))+''']
def offset : Fin 5 → Nat := ![0,9,12,21,26]
def coordinates (g : Fin 4) : List (Fin 26) :=
 (List.ofFn (fun c : Fin 26=>c)).filter (fun c=>offset g.castSucc≤c.val ∧ c.val<offset g.succ)
theorem bounds (g : Fin 4) : offset g.castSucc≤offset g.succ ∧ offset g.succ≤26 := by
 fin_cases g <;> decide
def groupModel (patterns : Fin 14 → K) (selectors : Fin 26 → K) (g : Fin 4) (s : Fin 4 → K) : Fin 4 → K :=
 fun j=>if g=j then s g+((coordinates g).map (fun c=>patterns (pattern c)*selectors c)).sum else s j
def inner (patterns : Fin 14 → NQ) (selectors : Fin 26 → NQ) (g : Fin 4) (s : State) : Result State :=
 NJB_StateUpdates.run (fun c state=>NJB_StateUpdates.mulAdd state g (patterns (pattern c)) (selectors c)) (coordinates g) s
theorem inner_result (patterns : Fin 14 → NQ) (selectors : Fin 26 → NQ) (g : Fin 4) (s : State)
 (hp : ∀ i,Canon (patterns i)) (ht : ∀ i,Canon (selectors i)) (hs : canonical s) :
 ∃ out,inner patterns selectors g s=ok out ∧ canonical out ∧
 decoded out=groupModel (fun i=>decode (patterns i)) (fun i=>decode (selectors i)) g (decoded s) := by
 obtain ⟨out,call,ho,vo⟩ := NJB_StateUpdates.run_result
  (fun c state=>NJB_StateUpdates.mulAdd state g (patterns (pattern c)) (selectors c))
  (fun c state=>addModel state g (decode (patterns (pattern c))*decode (selectors c)))
  (coordinates g) s hs (fun c _ before hb=>NJB_StateUpdates.mul_add_result before g _ _ hb (hp _) (ht _))
 refine ⟨out,call,ho,?_⟩
 funext j
 exact (congrFun vo j).trans (NJB_StateUpdates.sum_frame _ (coordinates g) (decoded s) g j)
def reference (patterns : Fin 14 → NQ) (selectors : Fin 26 → NQ) (s : State) : Result State :=
 NJB_StateUpdates.run (fun g state=>inner patterns selectors g state) (List.ofFn (fun g : Fin 4=>g)) s
def model (patterns : Fin 14 → K) (selectors : Fin 26 → K) (s : Fin 4 → K) : Fin 4 → K :=
 (List.ofFn (fun g : Fin 4=>g)).foldl (fun state g=>groupModel patterns selectors g state) s
/-- Both loop levels composed on the SAME raw state. Every actual field-call
Result and post-state frame is supplied by closed field laws in inner_result. -/
theorem result (patterns : Fin 14 → NQ) (selectors : Fin 26 → NQ) (s : State)
 (hp : ∀ i,Canon (patterns i)) (ht : ∀ i,Canon (selectors i)) (hs : canonical s) :
 ∃ out,reference patterns selectors s=ok out ∧ canonical out ∧
 decoded out=model (fun i=>decode (patterns i)) (fun i=>decode (selectors i)) (decoded s) :=
 NJB_StateUpdates.run_result _ _ _ s hs (fun g _ before hb=>inner_result patterns selectors g before hp ht hb)
#print result
#print axioms bounds
#print axioms inner_result
#print axioms result
end AspisR1.NJB_PatternReference
end
'''
(E/'NJB_PatternReference.lean').write_text(s);print('pattern raw reference: nested induction, full state/frame, frozen coordinate tables')
