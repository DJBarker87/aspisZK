import FJf_DotMeaning
import JFs_TX2_CheckedQ
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_EbyKCodec
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE qm wide)

theorem canon (q : NQ) (hq : FIo_QMValues.Canon q) :
    JFs_TX2_DotFinish.Canon (JFs_TX2_CheckedQ.value q) := by
  intro x hx
  change x∈[q.c0.a,q.c0.b,q.c1.a,q.c1.b] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl
  · exact hq.1.1
  · exact hq.1.2
  · exact hq.2.1
  · exact hq.2.2

theorem decoded (q : NQ) : FJf_RawDecode.q (JFs_TX2_CheckedQ.value q)=decodeQM (qm q) := rfl

def halves (v : NE) : Array FIo_Native.fast_pairing.canonical.Q 2#usize :=
  Array.make 2#usize [JFs_TX2_CheckedQ.value v.c0,JFs_TX2_CheckedQ.value v.c1]

theorem from_wide (v : NE) : FIo_Native.fast_pairing.canonical.Q.from_wide v=ok (halves v) := rfl

def model (s : FIo_Native.fast_pairing.EbyKDot) : AspisWideTower.WideExact :=
  ⟨FJf_RawDecode.dot s.c0,FJf_RawDecode.dot s.c1⟩

def scalar (q : NQ) : AspisWideTower.WideExact := ⟨decodeQM (qm q),0⟩

def Bound (s : FIo_Native.fast_pairing.EbyKDot) : Prop :=
  FJf_DotBound.Bound s.c0 s.count.val ∧ FJf_DotBound.Bound s.c1 s.count.val

#print axioms canon
#print axioms decoded
#print axioms from_wide
end AspisR1.FJf_EbyKCodec
end
