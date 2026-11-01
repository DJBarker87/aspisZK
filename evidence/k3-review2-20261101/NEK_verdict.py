"""Separate incomplete solver runs from semantic assertion failures."""
def verdict(log):
 text=log.lower()
 if 'timed out' in text or ('timeout' in text and 'VERIFICATION:- SUCCESSFUL' not in log):return 'OPEN'
 if 'unwinding assertion' in text or 'one or more unwinding failures' in text:return 'OPEN'
 if 'VERIFICATION:- SUCCESSFUL' in log:return 'PASS'
 if 'VERIFICATION:- FAILED' in log:return 'FAIL'
 return 'OPEN'
