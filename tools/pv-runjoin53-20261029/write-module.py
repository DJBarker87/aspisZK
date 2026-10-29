from pathlib import Path
import sys,os
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
def write(stem,imports,body,names):
 s='\n'.join('import '+n for n in imports)+'\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.'+stem+'\n'+body+'\n'+''.join('#print axioms '+n+'\n' for n in names)+'end R1Z.'+stem+'\n'
 p=L/(stem+'.lean')
 if os.environ.get('PV_RUNJOIN53_CHECK'):
  assert p.read_text()==s,stem
  print('matched',stem)
 else:
  assert not p.exists(),p
  p.write_text(s)
if __name__=='__main__':write(sys.argv[1],sys.argv[2].split(','),sys.stdin.read(),sys.argv[3].split(','))
