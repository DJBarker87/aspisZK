import S4ProductUpdateOfCountRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsPushProductTraceRootV1
open AspisR1DotCountBoundV1
abbrev State := AspisR1EbyKPushDotBackend.PushState
abbrev Wide := AspisR1EbyKPushDotBackend.PushWide
abbrev QM := AspisR1EbyKPushDotBackend.PushQm
abbrev M := AspisR1EbyKPushDecodedProductUpdate.M
abbrev T := M × M × M × M
abbrev S := T × T
abbrev raw := AspisR1EbyKPushDecodedProductUpdate.QRaw

def stateValue (s : State) : S :=
  (AspisR1EbyKPushDecodedProductUpdate.castSums s.c0.sums,
   AspisR1EbyKPushDecodedProductUpdate.castSums s.c1.sums)

def lowProduct (value : Wide) (scalar : QM) : T :=
  AspisR1.R22RawQmProductResidues.qmulCoefficients
    ((value.c0.c0.a.val,value.c0.c0.b.val),(value.c0.c1.a.val,value.c0.c1.b.val))
    ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))

def highProduct (value : Wide) (scalar : QM) : T :=
  AspisR1.R22RawQmProductResidues.qmulCoefficients
    ((value.c1.c0.a.val,value.c1.c0.b.val),(value.c1.c1.a.val,value.c1.c1.b.val))
    ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))

def addProduct (s : S) (vq : Wide × QM) : S :=
  (AspisR1EbyKPushDecodedProductUpdate.tupleAdd s.1 (lowProduct vq.1 vq.2),
   AspisR1EbyKPushDecodedProductUpdate.tupleAdd s.2 (highProduct vq.1 vq.2))

/-- Reuses the existing decoded one-push theorem and count invariant.
The returned field pair is exactly the ordered product accumulation of the
same accepted backend trace; no intermediate accumulator range is assumed. -/
theorem accepted_trace_product_sum
    (old out : State) (xs : List (Wide × QM))
    (h0 : sumsBelowCount old.count.val old.c0.sums)
    (h1 : sumsBelowCount old.count.val old.c1.sums)
    (hcanonical : ∀ p ∈ xs, AspisR1EbyKPowerValueCanonicalToPush.pushCanonical p.1)
    (htrace : AcceptedPushTrace raw old xs out) :
    stateValue out=xs.foldl addProduct (stateValue old) := by
  induction htrace with
  | nil s => rfl
  | @cons s mid out value scalar xs hpush htail ih =>
      have hc := hcanonical (value,scalar) (by simp)
      have hb := successful_push_preserves_count_bound raw s value scalar mid h0 h1 hpush
      have hs := AspisR1DotProductCountBridgeV1.successful_push_product_update_of_count
        s value scalar mid hc h0 h1 hpush
      have hstep : stateValue mid=addProduct (stateValue s) (value,scalar) := Prod.ext hs.1 hs.2
      have hrest : ∀ p ∈ xs, AspisR1EbyKPowerValueCanonicalToPush.pushCanonical p.1 :=
        fun p hp=>hcanonical p (List.mem_cons_of_mem _ hp)
      have ht := ih hb.1 hb.2.1 hrest
      change stateValue out=xs.foldl addProduct (addProduct (stateValue s) (value,scalar))
      rw [←hstep]
      exact ht
#print axioms accepted_trace_product_sum
end AspisR1FastDotsPushProductTraceRootV1
