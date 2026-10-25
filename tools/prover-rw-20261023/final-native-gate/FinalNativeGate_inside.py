"""Future fixed scope entry. Source-only version always disabled."""
def main():
    print('FinalNativeGate inside entry disabled; requires separate reviewed source patch')
    return 78

if __name__=='__main__':
    raise SystemExit(main())
