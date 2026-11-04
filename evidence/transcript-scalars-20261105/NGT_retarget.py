"""Canonical retarget of immutable actual scalar/absorb/block emission.
Only namespace, imports and explicit opaque callee parameters change.
The original emission and this deterministic transformation are evidence inputs.
"""
from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NGT_REUSED_TRANSCRIPT_Funs.lean.txt').read_text();s=s[s.index('namespace AspisR1Post25Transcript'):];s=s.replace('namespace AspisR1Post25Transcript','namespace AspisR1.NGT_Emitted\nopen AspisR1PublicPreparation').replace('end AspisR1Post25Transcript','end AspisR1.NGT_Emitted')
for n in ['absorb','block','scalar_k','scalar']:s=s.replace('transcript.Transcript.'+n,n)
for n in ['scalar_k','scalar']:
 s=s.replace('def '+n+'\n', 'def '+n+'\n  (B : PreparedModel.Boundaries) ')
s=s.replace('sampler.gamma_sample','B.gamma').replace('sampler.ordinary_sample','B.ordinary').replace('aspis_core.field.WideExact.from_qm31','B.fromQm')
s=s.replace('sampler.qm31_sample','AspisR1PublicPreparation.sampler.qm31_sample')
# trace.value is the identical no-op emitted in the adopted cohort.
a=s.index('/-- [aspis_r1_stage2_adopted_caller::trace::value]');b=s.index('/-- [aspis_r1_stage2_adopted_caller::transcript',a);s=s[:a]+s[b:]
(E/'NGT_Emitted.lean').write_text('import NFQ_STAGE2_IMPORT\nopen Aeneas Aeneas.Std Result\nset_option autoImplicit false\nnoncomputable section\n'+s)
