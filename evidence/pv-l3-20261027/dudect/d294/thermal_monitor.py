"""D294 evidence-only CPU sensor monitor; no sampling or marker mutation."""
import pathlib, time, json, sys
P = pathlib.Path
PACKAGE = P('/sys/class/thermal/thermal_zone5')
def sensors():
    assert (PACKAGE/'type').read_text().strip() == 'x86_pkg_temp'
    selected = [PACKAGE/'temp']
    for hw in P('/sys/class/hwmon').glob('hwmon*'):
        if (hw/'name').read_text().strip() != 'coretemp': continue
        for label in hw.glob('temp*_label'):
            name = label.read_text().strip()
            if name.startswith(('Package id ', 'Core ')):
                selected.append(label.with_name(label.name.replace('_label', '_input')))
    assert len(selected) > 1, 'coretemp inputs missing'
    return selected
def snapshot():
    temps = {str(p): int(p.read_text())/1000 for p in sensors()}
    return dict(epoch=time.time(), temperatures_c=temps,
                package_c=temps[str(PACKAGE/'temp')],
                cpu=2, scaling_cur_freq_khz=int(P('/sys/devices/system/cpu/cpu2/cpufreq/scaling_cur_freq').read_text()))
def excluded():
    # Do not read excluded temperature inputs, including the known ENODATA zone.
    return [dict(path=str(p/'temp'), type=(p/'type').read_text().strip(),
                 reason='excluded by CPU-only identity; iwlwifi_1 previously returned ENODATA' if (p/'type').read_text().strip()=='iwlwifi_1' else 'excluded by CPU-only identity')
            for p in P('/sys/class/thermal').glob('thermal_zone*') if p != PACKAGE]
if __name__ == '__main__':
    assert sys.argv[1:] == ['--dry-test-60s']
    assert not P('/home/dombarker/project-offloads/QUIET_WINDOW.json').exists(), 'dry test requires no window'
    start=time.monotonic()
    print(json.dumps(dict(kind='dry-test; no samples', excluded=excluded())), flush=True)
    while True:
        assert not P('/home/dombarker/project-offloads/QUIET_WINDOW.json').exists()
        print(json.dumps(snapshot()), flush=True)
        if time.monotonic()-start >= 60: break
        time.sleep(min(1, 60-(time.monotonic()-start)))
