from NIS_rerun import *
for row in json.loads((E/'NIS_RERUN_PLAN.json').read_text()):
 if (E/row['attempt']/'receipt.json').exists():continue
 try:run(row['attempt'],row['original'])
 except RuntimeError as err:
  print(json.dumps(dict(attempt=row['attempt'],finding=str(err))),flush=True)
  if not str(err).startswith('NIS-F'):raise
