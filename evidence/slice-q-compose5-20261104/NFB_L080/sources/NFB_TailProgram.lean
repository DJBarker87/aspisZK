import NFB_PeerAudit
set_option autoImplicit false
noncomputable section
namespace NFB_TailProgram
open Aeneas Aeneas.Std Result AspisR1
abbrev E := NEV_DotCarrier.NE
abbrev Q := NEV_DotCarrier.NQ
abbrev Dot := FIo_Native.fast_pairing.EbyKDot
abbrev Coeff := NEV_DotInputs.Coefficients

def first (q : Array U8 608#usize) (g : Coeff) (slot : Usize) : Result (E × Q) := do
 let e ← Array.index_usize g 28#usize
 let base ← slot*120#usize
 let start ← base+104#usize
 let stop ← base+120#usize
 let scalar ← NFA_TailQM.read q start stop
 ok (e,scalar)

def later (q : Array U8 608#usize) (g : Coeff) (stride position : Usize) : Result (E × Q) := do
 let base ← 480#usize+stride
 let delta ← position*16#usize
 let start ← base+delta
 let index ← position+26#usize
 let e ← Array.index_usize g index
 let stop ← start+16#usize
 let scalar ← NFA_TailQM.read q start stop
 ok (e,scalar)

def push (self : Dot) (e : E) (q : Q) : Result Dot := do
 let (r,next) ← FIo_Native.fast_pairing.EbyKDot.push self e q
 core.result.Result.unwrap core.fmt.DebugUnit r
 ok next

def run (q : Array U8 608#usize) (g : Coeff) (slot : Usize) : Result E := do
 let self ← FIo_Native.fast_pairing.EbyKDot.new
 let (e0,q0) ← first q g slot
 let self1 ← push self e0 q0
 let stride ← slot*32#usize
 let (e1,q1) ← later q g stride 0#usize
 let self2 ← push self1 e1 q1
 let (e2,q2) ← later q g stride 1#usize
 let self3 ← push self2 e2 q2
 FIo_Native.fast_pairing.EbyKDot.finish self3

/-- Pure bind reassociation, retaining the actual checked arithmetic order,
three SAME receiver transitions and every failure/divergence branch. -/
theorem association (q : Array U8 608#usize) (g : Coeff) (slot : Usize) :
 NFA_SuffixFactor.tail q g slot=run q g slot := by
 simp only [NFA_SuffixFactor.tail,run,first,later,push,NFA_TailQM.read,
  uncurry,bind_assoc_eq,bind_tc_ok]
 repeat' first
 | rfl
 | (apply (bind_eq_iff _ _ _).mpr
    intro x hx
    cases x
    simp only [uncurry,bind_assoc_eq,bind_tc_ok])

/-- A successful checked push exposes its SAME full actual Result/receiver. -/
theorem push_success (self after : Dot) (e : E) (q : Q) (accepted : push self e q=ok after) :
 FIo_Native.fast_pairing.EbyKDot.push self e q=ok (.Ok (),after) := by
 unfold push at accepted
 obtain ⟨⟨tag,next⟩,native,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 cases tag with
 | Err error => cases accepted
 | Ok unit =>
  cases unit
  simp only [core.result.Result.unwrap,bind_tc_ok] at accepted
  cases Result.ok.inj accepted
  exact native
#print axioms association
#print axioms push_success
end NFB_TailProgram
end
