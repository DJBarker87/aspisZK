from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NIV_ExtractedForward.lean').read_text();b=s[s.index('/-- [aspis_r1_cost_probe_program::r1_pool_adapter::process]'):s.index('\ntheorem process_source')]
b=b.replace('(ops : Hiq_DispatchSource.Ops Account)','(ops : Boundaries Account)')
for x,y in [('Hiq_DispatchSource.firstByte','ops.head'),('Hiq_DispatchSource.copied','ops.copy'),('Hiq_DispatchSource.eqU8','ops.eq'),('Hiq_DispatchSource.pool_route.admitted','ops.admitted')]:b=b.replace(x,y)
out='''import NIV_ExtractedForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIV_RawBoundary
open Aeneas Aeneas.Std Result
/-- Every opaque external retained as an explicit boundary; no axiom template
    is loaded. Only the concrete U8 instantiations reached by this body occur. -/
structure Boundaries (Account : Type) extends Hiq_DispatchSource.Ops Account where
  head : Slice U8 → Result (Option U8)
  copy : Option U8 → Result (Option U8)
  eq : {N : Usize} → Slice U8 → Array U8 N → Result Bool
  admitted : Slice U8 → Result Bool

def profile {Account : Type} (ops : Hiq_DispatchSource.Ops Account) : Boundaries Account where
  toOps := ops
  head := Hiq_DispatchSource.firstByte
  copy := Hiq_DispatchSource.copied
  eq := Hiq_DispatchSource.eqU8
  admitted := Hiq_DispatchSource.pool_route.admitted

'''+b+'''
/-- Profile specialization is a separate fact from realization of the opaque
    Rust primitive boundaries. Native realization is recorded OPEN. -/
theorem process_profile {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    process (profile ops) p a d = NIV_ExtractedForward.process ops p a d := rfl

theorem entry_profile {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    entry (profile ops) p a d = NIV_ExtractedForward.entry ops p a d := rfl

#print axioms process_profile
#print axioms entry_profile
end AspisR1.NIV_RawBoundary
end
'''
(E/'NIV_RawBoundary.lean').write_text(out)
