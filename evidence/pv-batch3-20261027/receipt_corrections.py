"""Annotate evidence-only base swaps without erasing the invocation revision."""
from pathlib import Path
import json
D=Path(__file__).resolve().parent
for label in ['fixture-bytes-build-base-01','fixture-bytes-run-base-01']:
 p=D/'receipts'/label/'receipt/receipt.json';x=json.loads(p.read_text())
 x['invocation_workspace_revision']=x['source_revision']
 x['effective_binary_source_revision']='37e5e133f89f4aa5909a1ca6fc81237d2c977947'
 x['source_revision_binding']='fixture-bytes-binary-base.json and fixture-base-files.json: all base-existing changed Rust/manifest files swapped from git show37e5e133f8 for build, then restored; unchanged inputs from base37 workspace; added modules unreachable from base manifests'
 x['source_revision_note']='raw scope envelope records current workspace freeze26ce27b295; effective base binary input revision is37e5e133f8. This annotation corrects that distinction without rerunning an unchanged fixture gate.'
 p.write_text(json.dumps(x,indent=2)+'\n')
