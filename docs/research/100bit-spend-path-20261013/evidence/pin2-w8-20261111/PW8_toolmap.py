"""PW8 tool-version name map (tool-option adaptation, Stream C class; separate from the recorded fe80/RPz7 identifier map).
Applied by script to the OLD-tool text (frozen gate: mirror-crate emission, old Aeneas; fe80 emission: Aeneas b59d5188-extended)
to express it in the second-tool (Aeneas 0d21a9ec) spelling used by PIN2_NEWGATE_r0/_r1_semantic. Each entry is a naming or
library-encoding difference only; none changes a value or a control path. The fresh side gets PCXU's xform (PW8_lib.xform)."""
import re
TOOL_MAP=[
 # (regex on old text, replacement, reason)
 (r'(?<![\w.])aspis_core\.Digest32(?![\w])','aspis_core.digest.Digest32','trait path: old tool flattened the re-export aspis_core::Digest32; second tool names the defining module aspis_core::digest'),
 (r'(?<![\w.])aspis_coreDigest32Inst(?![\w])','aspis_coredigestDigest32Inst','instance binder name derived from the trait path (same reason)'),
 (r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTryTraitFromResidualResultInfallible\.from_residual(?![\w])','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual','library encoding: old Aeneas residual over core.convert.Infallible; second tool over Never (PCWN_NewLib, castN/from_residual_eq in PIN2_NEWGATE_r0)'),
 (r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry\.branch(?![\w])','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch','library encoding: Try::branch model qualified to PCWN_NewLib (PCXU xform), branch_eq in PIN2_NEWGATE_r0'),
 (r'(?<![\w.])core\.result\.Result\.map_err(?![\w])','PCWN_NewLib.core.result.Result.map_err','library item qualified to PCWN_NewLib (PCXU xform; HM-C)'),
 (r'(?<![\w.«])public1(?![\w])','«public»','binder spelling of the Rust parameter `public` (keyword): old tool renamed to public1, second tool escapes with guillemets'),
 (r'\((H|Self|T|E|U) : Type\)','(\\1 : Type _)','universe annotation: second tool emits Type _'),
 (r'\{(H|Self|T|E|U) : Type\}','{\\1 : Type _}','universe annotation: second tool emits Type _'),
 (r'(?<![\w.])r1_wire\.Challenges(?![\w])','aspis_core.state_only_prefix.r0.Challenges','type path: the probe crate re-exports aspis_core::state_only_prefix::r0::Challenges as r1_wire::Challenges; mirror crate had its own copy (PCVL naming note: fields identical)'),
 (r'(?<![\w.«])record1(?![\w])','record','binder spelling of the Rust parameter `record`: old tool renamed to record1'),
 (r'(?<![\w.«])prefix1(?![\w])','«prefix»','binder spelling of the Rust parameter `prefix` (keyword): old tool renamed to prefix1, second tool escapes with guillemets'),
 (r'(?<![\w.])Isize(?![\w])','Std.Isize','namespace spelling of the discriminant carrier'),
]
def apply_tool_map(t,used=None):
    for i,(p,r,_) in enumerate(TOOL_MAP):
        t2=re.sub(p,r,t)
        if used is not None and t2!=t:used.add(i)
        t=t2
    return t
