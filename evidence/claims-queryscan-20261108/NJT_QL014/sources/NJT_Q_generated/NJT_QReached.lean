import NJT_QDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QReached
open Aeneas Aeneas.Std Result NJT_QBase
open Query31ExplicitListLoop

/-- Source-order carries on the SAME prior blocks. Continuation after a stop is
an overapproximation of reachability and strengthens coverage; it is never
used to alter the source's actual first-stop selection. -/
def carry (native : NJT_QScan.Native) : List Bytes → State → State
 | [],s => s
 | b::bs,s => carry native bs (NJT_QScan.run native (words b).val s).1

theorem carry_domain (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (prefix : List Bytes) (s : State) (domain : NJT_QDomains.Domain s) :
 NJT_QDomains.Domain (carry native prefix s) := by
 induction prefix generalizing s with
 | nil => exact domain
 | cons b bs ih => exact ih _ (NJT_QDomains.scan_preserved native cut b s domain)

/-- TX1:067 invocation root: all actual private caller carries start at default
and follow preceding SAME-block results. Its only Prop input is the reviewed
native word cut. Bounds/canonicality/inactive-zero are derived internally. -/
theorem scan (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (prefix : List Bytes) (block : Bytes) :
 let before:=carry native prefix NGQ_SamplerPacket.initial
 Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords before block=
  ok (optionStop (NJT_QScan.run native (words block).val before).2,
   (NJT_QScan.run native (words block).val before).1) ∧
 NJT_QDomains.Domain before ∧ NJT_QDomains.Domain (NJT_QScan.run native (words block).val before).1 := by
 have domain:=carry_domain native cut prefix NGQ_SamplerPacket.initial NJT_QDomains.initial
 exact ⟨NJT_QScan.scan native cut _ domain.1 block,domain,
  NJT_QDomains.scan_preserved native cut block _ domain⟩

#print axioms carry_domain
#print axioms scan
#check @scan
end AspisR1.NJT_QReached
end
