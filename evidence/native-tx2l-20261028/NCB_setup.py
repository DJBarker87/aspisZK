from pathlib import Path
import json
E=Path(__file__).resolve().parent;O=E.parent/'native-tx2i-20261028'
(E/'NCB_LAUNCHER_INPUTS.json').write_bytes((O/'NBS_LAUNCHER_INPUTS.json').read_bytes())
s=(O/'NBS_build.py').read_text().replace('NBS_','NCB_').replace('native-tx2i','native-tx2l')
s=s.replace("if len(list(E.glob('NCB_K*/receipt.json')))>=40:raise SystemExit('native budget exhausted; no additional prover launch')\n",'').replace('<=100','<=80').replace('<100','<80')
(E/'NCB_build.py').write_text(s)
s=(O/'NBS_kani.py').read_text().replace('NBS_','NCB_').replace('native-tx2i','native-tx2l').replace('<40','<70').replace('<100','<80')
s=s.replace("b=Path({B!r});p=b/", "b=Path({B!r});b.mkdir(exist_ok=True);p=b/")
s=s.replace("b=Path({B!r});s=Path({S!r})\nlaunchers", "b=Path({B!r});s=Path({S!r})\nif not s.exists():s.symlink_to('/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028/NBS_src',target_is_directory=True)\nlaunchers",1)
s += '''\nwith (E/'NCB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\\n')\n'''
(E/'NCB_kani.py').write_text(s)
s=(O/'NBS_expected.py').read_text()
s=s.replace("own=[];seen=set()", "own=[];seen=set()")
s=s.replace("for p in sorted(E.glob('NBS_K[0-9][0-9][0-9]-harness.patch')):","for p in sorted((E.parent/'native-tx2i-20261028').glob('NBS_K[0-9][0-9][0-9]-harness.patch'))+sorted(E.glob('NCB_K[0-9][0-9][0-9]-harness.patch')):")
(E/'NCB_expected.py').write_text(s)
