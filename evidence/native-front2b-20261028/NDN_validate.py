"""Run the unchanged NDK algorithm against an explicitly refreshed lane snapshot.
Only the immutable snapshot revision and output destinations are redirected.
This does not add an association recipe or promote NDN claims into global credit.
"""
from pathlib import Path
import sys,types,json
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E.parent/'native-ledger2-20261028'))
review_source=(E.parent/'native-ledger2-20261028/NDK_review.py').read_text()
review_source=review_source.replace("d['baseline_revision']=='898a8b0da7703af67b676b18b575236940830283'", "d['baseline_revision']=='7040c62270'")
review_source=review_source.replace("d['refresh']['other_merged_frontier_deltas']==[]", "d['refresh']['other_merged_frontier_deltas']==json.loads(NDN_REVIEW_PATH.read_text())['paths']")
module=types.ModuleType('NDK_review');module.__file__=str(E.parent/'native-ledger2-20261028/NDK_review.py')
module.__dict__['NDN_REVIEW_PATH']=E/'NDN_REVIEWED_INHERITED.json'
exec(compile(review_source,module.__file__,'exec'),module.__dict__);sys.modules['NDK_review']=module
s=(E.parent/'native-ledger2-20261028/NDK_validate.py').read_text()
s=s.replace("BASE = '898a8b0da7703af67b676b18b575236940830283'", "BASE = '7040c62270'")
s=s.replace("HERE / 'NDK_LEDGER.json'","HERE / 'NDN_LEDGER.json'").replace("HERE / 'NDK_LEDGER.md'","HERE / 'NDN_LEDGER.md'")
exec(compile(s,str(E/'NDN_validate.py'),'exec'),dict(__name__='__main__',__file__=str(E/'NDN_validate.py')))
