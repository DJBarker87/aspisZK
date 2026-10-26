"""Retained source-input decomposition, separately compiled from hash leaves."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1];old=R/'evidence/joint-fixture11-20261026/JFm_UNCHECKED'
s=(old/'JFm_Q25Source.lean.txt').read_text().replace('JFm_Q25','JFu_Q25').replace('import JFu_Q25Hashes','import JFu_Q25Aggregate\nimport JFu_Q25Reads');pos=s.index('theorem absorbInput')
files={R/'lean/JFu_Q25Input.lean':s[:pos]+'end AspisR1.JFu_Q25Source\n',R/'lean/JFu_Q25Source.lean':'import JFu_Q25Input\nset_option autoImplicit false\nnamespace AspisR1.JFu_Q25Source\nopen Aeneas Aeneas.Std Result\nopen AspisR1PublicPreparation\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge\n'+s[pos:]}
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('row25 source decomposition preflight:',len(files),'files; no hash compression evaluation')
