"""Run the unchanged NCZ validator algorithm on this lane's pinned snapshot.
Only snapshot, supplemental input and output names are redirected; no closure
rule is weakened. Existing global ledger and summary are never written.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
source=(E.parent/'native-compledger-20261028/NCZ_validate.py').read_text()
source=source.replace("BASE = '1d7752908191642fc8383c99bbadfb46fab8850c'", "BASE = 'b549ca928a'")
source=source.replace('NCZ_SUPPLEMENTAL.json','NDE_SUPPLEMENTAL.json').replace('NCZ_LEDGER.json','NDE_LEDGER.json').replace('NCZ_LEDGER.md','NDE_LEDGER.md')
exec(compile(source,str(E/'NDE_validate.py'),'exec'),dict(__name__='__main__',__file__=str(E/'NDE_validate.py')))
