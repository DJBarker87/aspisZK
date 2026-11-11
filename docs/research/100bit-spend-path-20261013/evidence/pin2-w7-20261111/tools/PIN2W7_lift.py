"""PIN2 W7: the release S1SemanticCode lift of public_transcript / SemanticTranscript.new,
re-targeted to the PIN2 emission by a fixed substitution table (recorded here; nothing else
in the text changes).  usage: python3 -I PIN2W7_lift.py <release.lean> <out.lean>"""
import sys
SUBS = [
  # module imports
  ('import RPz7_S1SemanticCodeSampleBlockV1\nimport RPz7_S1SemanticFinishModelV1\nimport RPz7_S1PreparedHashCodeV1\n',
   'import RPz7_S1PreparedHashCodeV1\nimport PIN2W7_PrefixGlue\n'),
  ('import RPz7_S1SemanticCodeNewTranscriptV1\nimport RPz7_S1SemanticCodeSampleBlockExactV1\n',
   'import PIN2_S1SemanticCodeNewTranscriptV1\n'),
  ('import RPz7_S1SemanticCodeNewTranscriptV1\nimport RPz7_S1SemanticFinishModelV1\nimport RPz7_S1PreparedHashCodeV1\n',
   'import PIN2_S1SemanticCodeNewTranscriptV1\n'),
  ('import RPz7_S1SemanticCodePublicTranscriptV1\nimport RPz7_S1SemanticCodeNewTranscriptExactV1\n',
   'import PIN2_S1SemanticCodePublicTranscriptV1\nimport PIN2_S1SemanticCodeNewTranscriptExactV1\n'),
  # namespace (declaration names unchanged)
  ('namespace AspisR1PublicPreparation.S1SemanticCode', 'namespace AspisR1PublicPreparationPIN2.S1SemanticCode\nopen AspisR1PublicPreparationPIN2'),
  ('end AspisR1PublicPreparation.S1SemanticCode', 'end AspisR1PublicPreparationPIN2.S1SemanticCode'),
  ('open PreparedHashCode (Code)', 'open AspisR1PublicPreparation.PreparedHashCode (Code)'),
  ('open PreparedHashCode\n', 'open AspisR1PublicPreparation.PreparedHashCode\n'),
  # trait path of the second tool (PW8_COMPARISON: aspis_core.Digest32 tool-option adaptation)
  ('aspis_core.Digest32', 'aspis_core.digest.Digest32'),
  # library names of the PIN2 emission (PCWN_NewLib, Never) in place of Aeneas.Std (Infallible)
  ('    core.result.Result.map_err\n', '    PCWN_NewLib.core.result.Result.map_err\n'),
  ('core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual',
   'PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual'),
  ('let cf ← core.result.Result.Insts.CoreOpsTry.branch', 'let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch'),
  # the Code monad's digest event is typed over the frozen Digest32: copy the instance at the event
  ('PreparedHashCode.effects.digest aspis_coreDigest32Inst hash s3',
   'AspisR1PublicPreparation.PreparedHashCode.effects.digest\n      (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack aspis_coreDigest32Inst) hash s3'),
]
src = open(sys.argv[1]).read()
out = src
used = []
for a, b in SUBS:
    if a in out:
        out = out.replace(a, b); used.append(a.split('\n')[0][:60])
hdr = ('/-! PIN2 W7 (2026-11-11): release ' + sys.argv[1].rsplit('/',1)[-1] +
       ' re-targeted to the PIN2 emission by tools/PIN2W7_lift.py (fixed substitution table: namespace, '
       'digest trait path, PCWN_NewLib branch/map_err/from_residual, digest-event instance copy). -/\n')
lines = out.split('\n'); k = 0
while lines[k].startswith('import'): k += 1
lines.insert(k, hdr.rstrip('\n'))
open(sys.argv[2], 'w').write('\n'.join(lines))
print(sys.argv[2].rsplit('/',1)[-1], 'substitutions:', len(used))
