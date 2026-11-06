import NJX_TailExpr
import NJX_WindowInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternTail
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_TailExpr (Expr)
open Expr
/-- Fourteen frozen assignments, in source order. Atoms0..15 are opened;
16..19 are windows0,1,2,8;20 is the public1051521018 lift. Corresponds
NJB_K104..131 (one-coordinate value/frame), NJL_K053/054 (all14 writes). -/
def expr : Fin 14 → Expr := ![
 .add (.atom 16) (.product 7 (.atom 19)),
 .atom 16,
 .sub (.sub (.atom 18) (.product 6 (.atom 8))) (.product 7 (.atom 9)),
 .sub (.sub (.atom 16) (.product 6 (.atom 6))) (.product 7 (.atom 7)),
 .add (.product 0 (.atom 0)) (.product 1 (.atom 1)),
 .add (.product 0 (.atom 6)) (.product 1 (.atom 7)),
 .product 0 (.atom 0),.product 0 (.atom 10),.product 0 (.atom 1),.product 0 (.atom 2),
 .add (.atom 19) (.product 7 (.atom 20)),.atom 18,.atom 17,.atom 19]
def State := Fin 14 → NQ
def write (s : State) (j : Fin 14) (x : NQ) : State := fun i=>if i=j then x else s i
/-- Transcription of each NJB tail native post-state; replies are not
interpreted here. At the root eval supplies all actual arithmetic Results. -/
def Cut (s after : State) (j : Fin 14) (reply : NQ) : Prop :=
 ∀ i,after i=if i=j then reply else s i

def run {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (a : Fin 21 → NQ) : List (Fin 14) → State → Result State
 | [],s => ok s
 | j::js,s => do
   let x ← NJX_TailExpr.eval p a (expr j)
   run p a js (write s j x)

inductive Trace {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (a : Fin 21 → NQ) : List (Fin 14) → State → State → Prop
 | nil (s) : Trace p a [] s s
 | cons (j js s x middle after) : NJX_TailExpr.eval p a (expr j)=ok x →
   Cut s middle j x → Trace p a js middle after → Trace p a (j::js) s after

/-- Finite ordered frame chain; every changed and unchanged cell is retained. -/
theorem source {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (a : Fin 21 → NQ)
 (ha : ∀ i,Canon (a i)) (js : List (Fin 14)) (s : State) (hs : ∀ i,Canon (s i)) :
 ∃ out,run p a js s=ok out ∧ Trace p a js s out ∧ (∀ i,Canon (out i)) ∧
 ∀ i,decode (out i)=if i∈js then NJX_TailExpr.value (decode lambda) (fun k=>decode (a k)) (expr i) else decode (s i) := by
 induction js generalizing s with
 | nil => exact ⟨s,rfl,.nil s,hs,by intro i;simp⟩
 | cons j js ih =>
   obtain ⟨x,cx,hx,vx⟩ := NJX_TailExpr.source p a ha (expr j)
   have hm : ∀ i,Canon (write s j x i) := by intro i;unfold write;split <;> simp_all
   obtain ⟨out,co,tr,ho,vo⟩ := ih (write s j x) hm
   refine ⟨out,by simp only [run,cx,bind_tc_ok,co],.cons j js s x (write s j x) out cx (by intro i;rfl) tr,ho,?_⟩
   intro i
   rw [vo]
   by_cases hij : i=j
   · subst i
     simp only [List.mem_cons,self_eq_true,true_or,if_true,write]
     split <;> simp_all
   · simp only [List.mem_cons,hij,false_or,write,if_neg hij]
#print source
#print axioms source
end AspisR1.NJX_PatternTail
end
