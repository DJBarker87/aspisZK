import NKG_OracleCuts
import NKG_InternalChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_GroupFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open FJh_Base (State cell)
open NKG_OracleCuts (Packed Three Prepared)
open NKG_InternalChoices (get)
def index (g : Fin 4) : Usize := Usize.ofNat g.val (by have := g.isLt;scalar_tac)
def start (g : Fin 4) : Usize := Usize.ofNat (4*g.val) (by have := g.isLt;scalar_tac)
def stop (g : Fin 4) : Usize := Usize.ofNat (4*g.val+4) (by have := g.isLt;scalar_tac)
def pack (a : State) (g : Fin 4) : NQ := get
 (field.qm31_pack_base4 (FJh_GroupSlices.sliceAt a (start g) (stop g))) field.QM31.ZERO
def sub (x y : NQ) : NQ := get (field.QM31.sub x y) field.QM31.ZERO
def differences (target ip : NQ) (lead full : Packed) (g : Fin 4) : Three :=
 Array.make 3#usize [sub target (cell lead g),sub target (cell full g),sub target ip]
def sum (p : Prepared) (d : Three) : NQ := get (field.qm31_sum_products3_prepared p d) field.QM31.ZERO
def mul (p : NP) (x : NQ) : NQ := get (field.PreparedQm31Multiplier.mul p x) field.QM31.ZERO
def model (succ internal : State) (lead full : Packed) (p : Prepared) (block : NP) (g : Fin 4) : NQ :=
 mul block (sum p (differences (pack succ g) (pack internal g) lead full g))
structure Observation where
 target : NQ
 ip : NQ
 differences : Three
 sum : NQ
 out : NQ
 packInputs : Fin 2 → Packed
 subArgs : Fin 3 → Fin 2 → NQ
 sumCaches : Prepared
 sumRight : Three
 mulCache : NP
 mulRight : NQ
 packCalls : Nat
 subCalls : Nat
 sumCalls : Nat
 mulCalls : Nat
/-- Only the four verified K023 replacement cuts. All child replies are the
literal CLOSED emitted operations; no arbitrary dictionary or child law field. -/
structure Frame (succ internal : State) (lead full : Packed) (p : Prepared) (block : NP)
 (g : Fin 4) (o : Observation) : Prop where
 packs : NKG_OracleCuts.Pack succ internal g o.packInputs
   (fun c=>if c.val=0 then pack succ g else pack internal g) o.target o.ip o.packCalls
 subs : NKG_OracleCuts.Sub o.target o.ip lead full g o.subArgs
   (differences o.target o.ip lead full g) o.differences o.subCalls
 sums : NKG_OracleCuts.Sum p o.sumCaches o.differences o.sumRight
   (sum p o.differences) o.sum o.sumCalls
 multiply : NKG_OracleCuts.Mul block o.mulCache o.sum o.mulRight
   (mul block o.sum) o.out o.mulCalls
/-- Native segment post-state is the next segment's SAME pre-state. -/
theorem result (succ internal : State) (lead full : Packed) (p : Prepared) (block : NP)
 (g : Fin 4) (o : Observation) (cut : Frame succ internal lead full p block g o) :
 o.out=model succ internal lead full p block g := by
 have target := cut.packs.targetReply
 have ip := cut.packs.internalReply
 change o.target=pack succ g at target
 change o.ip=pack internal g at ip
 have ds := cut.subs.returned
 have sm := cut.sums.returned
 have out := cut.multiply.returned
 rw [out,sm,ds,target,ip]
 rfl
#print result
#print axioms result
#print Frame
end AspisR1.NKG_GroupFrame
end
