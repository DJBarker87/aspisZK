import NKF_BoxModel
set_option autoImplicit false
noncomputable section
namespace NKF_MasterBox
open Aeneas Aeneas.Std Result
abbrev M := NJQ_Carrier.CM
abbrev F := NJQ_Carrier.CF
/-- SAME arguments, complete raw law, wrapper error map, safe Box value model.
The pure carrier is the canonical slot48 carrier; no free operation dictionary. -/
def reference (b : Slice U8) := NKF_BoxModel.outer (NJQ_Canonical.master b)

theorem raw_child (b : Slice U8)
 (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (cut : NJQ_MasterTotal.Cut b raw) :
 ok (NKF_BoxModel.tail (NJQ_Carrier.master_result raw)) = reference b := by
 exact NKF_BoxModel.congruence _ _ (NJQ_Canonical.master_result b raw cut)

/-- Typed native tail predicate. This equation is licensed only by the
universal wrapper tail cut/controls, not by a successful child or endpoint. -/
def TailCut (raw : core.result.Result M F)
 (out : core.result.Result M NKF_BoxModel.PE) : Prop :=
 out = NKF_BoxModel.tail raw

theorem source (b : Slice U8)
 (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (rawCut : NJQ_MasterTotal.Cut b raw)
 (out : core.result.Result M NKF_BoxModel.PE)
 (native : TailCut (NJQ_Carrier.master_result raw) out) :
 ok out = reference b := by
 rw [native]
 exact raw_child b raw rawCut

set_option pp.proofs false in
#print raw_child
#print axioms raw_child
set_option pp.proofs false in
#print source
#print axioms source
end NKF_MasterBox
