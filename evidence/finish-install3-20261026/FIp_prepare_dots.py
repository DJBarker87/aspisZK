from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
D=R/'docs/research/100bit-spend-path-20261013'
parser=D/'lean/CandidateFieldParsers.lean'
s=parser.read_text();s=s[s.index('/-- Source-bound Option'):s.index('/-- [aspis_core::parse_fields_probe]')]
# Reuse only the source operations; no proof options or duplicate field records.
s=s.replace('theorem optionTag_none (T : Type) : optionTag (none : Option T) = 0#isize := rfl','').replace('theorem optionTag_some {T : Type} (x : T) : optionTag (some x) = 1#isize := rfl','')
s='''import FIo_Install
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1.FIp_DotDecode
abbrev field.M31 := U32
abbrev field.CM31 := FIo_Native.aspis_core.field.CM31
abbrev field.QM31 := FIo_Native.aspis_core.field.QM31
'''+s+'''
#print axioms field.M31.from_le_bytes
#print axioms field.QM31.from_le_bytes
end AspisR1.FIp_DotDecode
'''
(R/'lean/FIp_DotDecode.lean').write_text(s)
source=D/'lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/evidence/generated/AspisR1FastDotsMinimalFixedCallsV10/Funs.lean'
s=source.read_text();s=s[s.index('/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]'):s.index('end AspisR1FastDotsMinimalFixedCallsV10')]
s=s.replace('aspis_core.field.','FIo_Native.aspis_core.field.').replace('fast_pairing.EbyKDot','FIo_Native.fast_pairing.EbyKDot')
s=s.replace('FIo_Native.aspis_core.field.M31.from_le_bytes','AspisR1.FIp_DotDecode.field.M31.from_le_bytes').replace('FIo_Native.aspis_core.field.QM31.from_le_bytes','AspisR1.FIp_DotDecode.field.QM31.from_le_bytes')
s='''import FIp_DotDecode
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1.FIp_NativeDots
'''+s+'''
#print axioms fast_dots.four_dots
end AspisR1.FIp_NativeDots
end
'''
(R/'lean/FIp_NativeDots.lean').write_text(s)
actual=R/'crates/aspis-r1-cost-probe/src/fast_dots.rs';retained=D/'lean-candidates/s4-minimal-fixed-calls-v10-20261021/fast_dots.rs'
assert actual.read_bytes()==retained.read_bytes()
sha=lambda p:dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
(E/'FIp_DotsPins.json').write_text(json.dumps(dict(actual=sha(actual),retained=sha(retained),generated=sha(source),decoder=sha(parser),adapted=[sha(R/'lean/FIp_DotDecode.lean'),sha(R/'lean/FIp_NativeDots.lean')],adaptation='Only operation/type namespace substitution to concrete FIo native arithmetic and source-derived decoder; no template/axiom imported. No source-to-ELF replay claimed.'),indent=2)+'\n')
