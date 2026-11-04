"""Add exact direct-use inventory and explicit nominal-owner distinctions."""
from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;x=json.loads((E/'NGK_PROVENANCE.json').read_text());rename=x['namespace_map']
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
uses=[]
for r in x['files']:
 for t in sorted(set(re.findall(r'(?<![\w.])[A-Z][\w]*(?:\.[\w]+)+',r['before_body']))):uses.append(dict(consumer=r['source_module'],before=t,after=pat.sub(lambda m:rename[m.group()],t)))
(E/'NGK_DECLARATION_USES.json').write_text(json.dumps(uses,indent=1)+'\n')
p=E/'NGK_FAMILIES.md';text=p.read_text().split('\n## Definitional equality and direct uses')[0]
text+='''
## Definitional equality and direct uses

| Family | Legacy → canonical | Equality / transport disposition |
|---|---|---|
| GuardBody/S2Sdk* | RPz7_* via existing canonical proof chains | Competing module owners cannot load together (NGJ_L027). No cross-owner definitional equality asserted; consume canonical proofs read-only. |
| Prepared/PrepQM | RPz7_PreparedFromQmSourceBridge and its consumers | Nominal carrier ownership differs (NGJ_L028); no rfl across duplicate owners. Entire canonical producer/consumer chain reused. |
| Phase | AspisR1PublicPreparation.Types via RPz7 and NFN/NFS | Different inductive owners (NGJ_L029), not admitted as definitionally equal. No legacy Phase introduced. |
| NED/NBN/NBK library | NFY/NGE/NGF module/namespace mapping above | Existing canonical retarget proofs reused; exact namespace substitution recorded, no new theorem transported by an assumed equality. |
| NFO/NFR/NFV local carriers | NGK_NFO/NGK_NFR/NGK_NFV | Renamed nominal inductives are not definitionally equal to legacy carriers. ALL local producers/consumers retarget together; no old/new cast or equality premise. |
| Decoder map_err | AspisR1TerminalDecoder.core.result.Result.map_err | NFY_OwnerTransport.map_err_transport proves complete Result equality (including failure/divergence) to canonical installed helper, by rfl. Seven Pool copies require qualified emitted names; recorded before/after statements. |
| Other admitted dependencies | Identical already-loaded module names | Same canonical constants in final environment, no duplicated shared owner or assumed transport. Exact object hashes are pinned per attempt. |

The three exact conflicting declarations reached indirectly by the Pool closure
were `AspisS2OwnedStage1.SdkReference.GuardBody.tacticSdk_finish_guard_write`,
`AspisR1PublicPreparation.PreparedFromQmSourceBridge.PrepQM`, and
`AspisR1PublicPreparation.verifier.Phase`. The exact two import paths and
object pins for each remain in the immutable NGJ_CONFLICTS.json input. Legacy
and canonical copies do not form a simultaneously loadable environment, so
NGK does not claim an untested cross-environment definitional equality. Its
canonical dependency replacement avoids that ill-formed join entirely.

NGK_DECLARATION_USES.json enumerates every qualified direct token with exact
before/after names. Unqualified uses are retained in full pinned bodies and
resolved by the compiler; the full import closure is not shortened to lexical
uses. NGK_CERTIFICATES.json enumerates all selected predecessor audit records
and source theorem declarations before consulting a loaded-module graph.
'''
p.write_text(text)
