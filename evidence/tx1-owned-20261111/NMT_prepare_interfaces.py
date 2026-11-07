from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for fn in ['tx1','first','stage1_owned']:
 raw=E/'NMT_extracted'/fn/'raw'/('NMT_'+fn)
 if not raw.is_dir():continue
 subprocess.run(['python3',str(E/'NMT_parameterize.py'),fn,'--raw',str(raw.relative_to(E))],check=True)
 for stem in ['Types','Funs']:
  (E/('NMT_'+fn+'.'+stem+'.lean')).write_bytes((E/'NMT_lean'/('NMT_'+fn)/(stem+'.lean')).read_bytes())
