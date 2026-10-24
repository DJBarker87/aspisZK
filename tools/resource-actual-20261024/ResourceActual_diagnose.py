"""Nonmutating complete cell diagnostics; does not turn rejected inputs into GO."""
import json
from pathlib import Path
import runpy

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-actual-20261024'
BASE=ROOT/'tools/resource-stat-20261024'


def diagnose(snapshot,code):
    violations=[]
    rows=snapshot['rows']
    for row in rows:
        if not row['enabled']:continue
        children=[c for c in rows if c['parent']==row['path'] and c['enabled']]
        usage=row['current']-sum(c['current'] for c in children)
        if usage<0:violations.append(dict(path=row['path'],field='current',parent=row['current'],children=sum(c['current'] for c in children),exclusive=usage))
        for field in code['REQUIRED']:
            value=row['stat'][field]-sum(c['stat'][field] for c in children)
            if value<0 or value>usage:
                violations.append(dict(path=row['path'],field=field,parent=row['stat'][field],children=sum(c['stat'][field] for c in children),exclusive=value,exclusive_current=usage))
    try:
        result=code['accounting'](snapshot)
        accounting=dict(accepted=True,result=result)
    except (ValueError,KeyError,TypeError) as exc:
        accounting=dict(accepted=False,error=f'{type(exc).__name__}: {exc}')
    return dict(accounting=accounting,individual_violations=violations)


def main():
    name='prospective-report.json' if (OUT/'prospective-report.json').exists() else 'prospective-report-summary.json'
    report=json.loads((OUT/name).read_text())
    code=runpy.run_path(str(BASE/'ResourceStat_candidate.py'))
    result={phase:diagnose(snapshot,code) for phase,snapshot in report['snapshots'].items() if snapshot}
    print(json.dumps(dict(snapshots=result,live_decision=report['decision']['allowed'],
        retained_error=report['decision'].get('error'),interpretation='Offline rejection diagnosis only; no changed inputs or live retry'),indent=2,sort_keys=True))

if __name__=='__main__':main()
