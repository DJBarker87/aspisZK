import NJZ_Readers
import NJJ_Constructors
set_option autoImplicit false
noncomputable section
namespace NKK_NativeRaw
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev Reader := verifier.Reader

/-- Value and complete immutable frame of one RawOracle event.
NKK_parent::frame asserts cursor/pointer/length and an arbitrary backing byte;
NKK_parent query_chunk8/query_chunk6 assert each from_le_bytes result.
The child is instantiated by NJZ_Readers.raw_cut at this SAME Reader. -/
def Step (n : Usize) (before after : Reader) (reply : Array U8 n) : Prop :=
 NJZ_Readers.RawCut n before after reply

/-- A source-ordered fold. The next Reader comes from this event's actual
reply, never from an independently chosen successful run. -/
def reads (n : Usize) : Nat → Reader → Result (List (Array U8 n) × Reader)
 | 0,r => ok ([],r)
 | count+1,r => do
   let (b,next) ← NJC_ConcreteUnwrap.raw n r
   let (bs,last) ← reads n count next
   ok (b::bs,last)

/-- Child-instantiated Reader chain. The native segment frame/order cut is
separate: RawCut includes the CLOSED child law, not only native assertions. -/
inductive Chain (n : Usize) : Reader → List (Array U8 n) → Reader → Prop where
 | nil (r : Reader) : Chain n r [] r
 | cons {r next last : Reader} {b : Array U8 n} {bs : List (Array U8 n)}
   (step : Step n r next b) (tail : Chain n next bs last) : Chain n r (b::bs) last

theorem backing {n : Usize} {r last : Reader} {bs : List (Array U8 n)}
 (chain : Chain n r bs last) : last.bytes=r.bytes := by
 induction chain with
 | nil => rfl
 | cons step tail ih => exact ih.trans step.2.2

theorem advance {n : Usize} {r last : Reader} {bs : List (Array U8 n)}
 (chain : Chain n r bs last) : last.at.val=r.at.val+n.val*bs.length := by
 induction chain with
 | nil => simp
 | cons step tail ih =>
  have h := step.2.1
  simp only [List.length_cons,Nat.mul_succ]
  omega

/-- Read Result plus the cut at the SAME arguments. The bounded-domain clause
is a local caller fact, not assumed successful decoding. -/
theorem one (n : Usize) (r : Reader)
 (bound : r.at.val+n.val≤r.bytes.val.length) :
 ∃ b next, Step n r next b ∧ NJC_ConcreteUnwrap.raw n r=ok (b,next) :=
 NJZ_Readers.raw_cut n r bound

#print axioms backing
#print axioms advance
#print axioms one
end NKK_NativeRaw
