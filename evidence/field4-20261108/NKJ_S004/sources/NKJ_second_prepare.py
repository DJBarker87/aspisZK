from pathlib import Path
import shutil
b=Path(__file__).resolve().parent
shutil.copytree(b/'NKJ_audit',b/'NKJ_audit1')
print('NKJ first audit preserved; second pass justified by new cohort-operation law')
