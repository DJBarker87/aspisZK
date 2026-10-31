"""Canonicalize identical reference-only enum owners; no Rust/harness name changes."""
from pathlib import Path
import hashlib,json,re,sys
E=Path(__file__).resolve().parent;check='--check' in sys.argv
canonical=E/'NEC_Reference/Types.lean'
schema='inductive ChildError (E : Type) where\n| Child : E → ChildError E'
assert schema in canonical.read_text()
rows=[]
for module in ['NEC_PairRef','NEC_ReplyRef']:
 p=E/module/'Types.lean';old=p.read_text()
 expected=f'''-- Canonical owner normalization of the identical reference-only error schema.
-- Original generated source and hashes are retained in NEC_OWNER_NORMALIZATION.json.
import NEC_Reference.Types
set_option autoImplicit false
namespace {module}
abbrev ChildError (E : Type) := NEC_Reference.ChildError E
namespace ChildError
abbrev Child {{E : Type}} (error : E) : {module}.ChildError E :=
 NEC_Reference.ChildError.Child error
end ChildError
end {module}
'''
 if check:assert old==expected,module
 else:
  assert schema in old,module
  snap=E/'NEC_owner_snapshot'/module/'Types.lean.txt';snap.parent.mkdir(parents=True,exist_ok=True);snap.write_text(old)
  p.write_text(expected)
 rows.append(dict(module=module,canonical_owner='NEC_Reference.Types',original_sha256=hashlib.sha256((E/'NEC_owner_snapshot'/module/'Types.lean.txt').read_bytes()).hexdigest(),normalized_sha256=hashlib.sha256(expected.encode()).hexdigest(),change='Replace identical duplicated inductive/auto-global instance by canonical type/constructor aliases. Generated functions and final wrapper statements unchanged.'))
if not check:(E/'NEC_OWNER_NORMALIZATION.json').write_text(json.dumps(rows,indent=1)+'\n')
print('canonical reference owners verified')
