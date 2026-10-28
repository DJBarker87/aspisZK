from pathlib import Path
import shutil,json
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028');F=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028')
for name in ['project-native-inputs.json','structural-inputs.json']:
 shutil.copyfile(F/name,D/name)
(D/'src').symlink_to(F/'src',target_is_directory=True)
(D/'classification-inputs').mkdir(exist_ok=True)
for p in (F/'classification-inputs').glob('*'):
 if p.is_file():shutil.copyfile(p,D/'classification-inputs'/p.name)
