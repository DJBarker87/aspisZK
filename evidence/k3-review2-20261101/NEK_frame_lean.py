"""Focused generic frame proof; no native certificate is inferred from this file."""
from NEK_lean import *
from NEK_scan import read_json
def run():
 a='NEK_L004';name='NEK_WindowFrames.lean'
 assert not (E/a/'receipt.json').exists()
 admit('NEK_FRAME_LEAN_INPUT')
 gate=(E/'NEK_lean_gate.py').read_text().replace('NEK_L001_LIBRARY_PINS.json','NEK_L004_LIBRARY_PINS.json').replace('NEK_ByteWindows.lean',name)
 r=py(f'''from pathlib import Path
b=Path({B!r});(b/{name!r}).write_text({(E/name).read_text()!r});(b/'NEK_frame_gate.py').write_text({gate!r})
''');assert r.returncode==0
 cfg=read_json(E/'NEK_L001.json');cfg.update(attempt=a,module=name,sources=[name,'NEK_frame_gate.py','lakefile.toml','lean-toolchain','lake-manifest.json'],command=['python3','NEK_frame_gate.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='focused Init-only symbolic disjointness/frame composition; no generated recurrence, no native bridge credit',print_axioms=['NEK_WindowFrames.'+n for n in ['writeAt_selected','writeAt_frame','disjoint_writes','window_and_frame_ext','finite_windows_ext']])
 launch(cfg)
 if read_json(E/a/'receipt.json')['exit_status']!=0:raise SystemExit('Lean compilation failed; no credit')
 r=py(f"from pathlib import Path;print((Path({B!r})/'NEK_L004_LIBRARY_PINS.json').read_text())");assert r.returncode==0;(E/'NEK_L004_LIBRARY_PINS.json').write_text(r.stdout)
if __name__=='__main__':run()
