import NJL_CacheReads
import NJB_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_TailExpr
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
inductive Expr where
 | atom : Fin 21 → Expr
 | product : Fin 8 → Expr → Expr
 | add : Expr → Expr → Expr
 | sub : Expr → Expr → Expr

def eval {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (a : Fin 21 → NQ) : Expr → Result NQ
 | .atom i => ok (a i)
 | .product i e => do
   let x ← eval p a e
   FIq_Native.field.PreparedQm31Multiplier.mul (NJL_CacheReads.cache p i) x
 | .add e f => do
   let x ← eval p a e
   let y ← eval p a f
   FIq_Native.field.QM31.add x y
 | .sub e f => do
   let x ← eval p a e
   let y ← eval p a f
   FIq_Native.field.QM31.sub x y

def value (lambda : K) (a : Fin 21 → K) : Expr → K
 | .atom i => a i
 | .product i e => lambda^(i.val+1)*value lambda a e
 | .add e f => value lambda a e+value lambda a f
 | .sub e f => value lambda a e-value lambda a f

/-- Same actual cache on every product; constructor domains come from p.
This generic lemma is SUPPORT, never a new caller hypothesis. -/
theorem source {lambda : NQ} (p : NJL_CachedPowers.Packet lambda)
 (a : Fin 21 → NQ) (ha : ∀ i,Canon (a i)) (e : Expr) :
 ∃ out,eval p a e=ok out ∧ Canon out ∧ decode out=value (decode lambda) (fun i=>decode (a i)) e := by
 induction e with
 | atom i => exact ⟨a i,rfl,ha i,rfl⟩
 | product i e ih =>
   obtain ⟨x,cx,hx,vx⟩ := ih
   obtain ⟨out,co,ho,vo⟩ := NJB_PreparedLaws.mul_result (NJL_CacheReads.cache p i) (NJL_CacheReads.power p i) x
    (NJL_CacheReads.canonical p i) hx (NJL_CacheReads.constructor p i).2
   exact ⟨out,by simp only [eval,cx,bind_tc_ok,co],ho,by rw [vo,NJL_CacheReads.value,vx];rfl⟩
 | add e f ihe ihf =>
   obtain ⟨x,cx,hx,vx⟩ := ihe
   obtain ⟨y,cy,hy,vy⟩ := ihf
   obtain ⟨out,co,ho,vo⟩ := NJB_StubLaws.qm_add x y hx hy
   exact ⟨out,by simp only [eval,cx,cy,bind_tc_ok,co],ho,by rw [vo,vx,vy];rfl⟩
 | sub e f ihe ihf =>
   obtain ⟨x,cx,hx,vx⟩ := ihe
   obtain ⟨y,cy,hy,vy⟩ := ihf
   obtain ⟨out,co,ho,vo⟩ := NJB_StubLaws.qm_sub x y hx hy
   exact ⟨out,by simp only [eval,cx,cy,bind_tc_ok,co],ho,by rw [vo,vx,vy];rfl⟩
#print source
#print axioms source
end AspisR1.NJX_TailExpr
end
