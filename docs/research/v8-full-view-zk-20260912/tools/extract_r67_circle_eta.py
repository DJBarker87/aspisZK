#!/usr/bin/env python3
"""Extraction-only eta expansion of two pure conversion function items.
No runtime-stage or repository protocol file is modified. Record the exact
original and transformed sources; do not describe them as byte-identical.
"""
from pathlib import Path
here = Path(__file__).parent
source = (here/'extract_r67_circle.py').read_text()
normalization = '''
original=a.output/'original';original.mkdir()
target=source/'r24_guarded_qm.rs'
assert sha(target)=='3d9eb8495212e2dd95d5235034fd0f7e19f8cf7c5fc0d08e84615cb708425fa1'
shutil.copy2(target,original/target.name)
before=target.read_text()
assert before.count('.map(u64::from)')==2
after=before.replace('.map(u64::from)','.map(|value| u64::from(value))')
target.write_text(after)
(a.output/'normalization.json').write_text(json.dumps({
 'rule':'eta expansion of pure noncapturing u32-to-u64 conversion in array.map',
 'before_sha256':sha(original/target.name),'after_sha256':sha(target),
 'sites':2,'runtime_source_changed':False,
 'trust_boundary':'audited extraction-only normalization; not a verified Rust compiler'
},indent=2)+'\\n')
'''
# Execute the retained recipe with this one explicitly recorded pre-extraction step.
source = source.replace("exec(compile(source,str(here/'extract_r64_field.py'),'exec'))",
    "source=source.replace('env=dict(os.environ',normalization+'\\nenv=dict(os.environ')\n"
    "exec(compile(source,str(here/'extract_r64_field.py'),'exec'))")
exec(compile(source,str(here/'extract_r67_circle.py'),'exec'))
