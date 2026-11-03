from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
source=(E/'NEI_COMPOSE_TESTS.py').read_text()
checkpoint=json.loads((E/'NEI_COMPOSE_TESTS_FAILED.json').read_text())
assert hashlib.sha256(source.encode()).hexdigest()==checkpoint['source_sha256']
head=source[:source.index("reject('wrong caller body'")]
tail=source[source.index('static_edge='):]
exec(compile(head,str(E/'NEI_COMPOSE_TESTS.py'),'exec'))
results[:]=checkpoint['completed_prefix']
exec(compile(tail,str(E/'NEI_COMPOSE_TESTS.py')+':remaining-cases','exec'))
