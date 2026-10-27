from pathlib import Path
import re,json,hashlib
E=Path(__file__).parent;p=Path('docs/research/100bit-spend-path-20261013/evidence/s9-wide-exact-mul-source-cut-v1-20261022/evidence/aeneas/generated/AspisR1S9ActualWideMulCutV1/Funs.lean');s=p.read_text()
start=s.index('def field.M31.add');end=s.index('/-- [s9_helper_actual_field_types_cut::field::wide_exact::{');body=s[start:end]
body=re.sub(r'@\[[\s\S]*?\]\s*(?=def)', '',body)
head='''import Aeneas
import XRh_Release.Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace XRj_Field
abbrev field.M31 := XRh_Release.aspis_core.field.M31
abbrev field.CM31 := XRh_Release.aspis_core.field.CM31
abbrev field.QM31 := XRh_Release.aspis_core.field.QM31
/- Definitions below reused from SOURCE (through mul_u), with namespace only.
 SOURCE: '''+str(p)+'''
 Field source-to-release association remains separate from these definitions. -/
def field.P : U32 := 2147483647#u32
'''
(E/'XRj_Field.lean').write_text(head+body+'\nend XRj_Field\n')
