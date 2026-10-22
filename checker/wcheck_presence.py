#!/usr/bin/env python3
"""Completes a distributed check of a worm certificate: every part 0..nparts-1 is present in MERGED (npy, json, leaves),
all headers agree (family, gid_map, tau, split0, nparts, lo, hi, maxsmall), and every part has a check-log line from
wcheck.py with ok = true whose sha256 of the three part files equals the merged copy's.
  wcheck_presence.py MERGED CHECKLOG [CHECKLOG ...]"""
import sys, os, json, hashlib
if not __debug__:
    raise SystemExit('run without -O')
merged = sys.argv[1]
logs = {}
for f in sys.argv[2:]:
    for line in open(f):
        if line.startswith('{'):
            r = json.loads(line)
            if r.get('ok'):
                logs.setdefault(int(r['part']), []).append(r)
first = json.load(open(os.path.join(merged, 'part0000.json')))
NP = int(first['nparts'])
keys = ('famspec', 'gid_map', 'tau', 'split0', 'nparts', 'lo', 'hi', 'maxsmall')
bad = []; leaves = 0; minm = None
for p in range(NP):
    files = {ext: os.path.join(merged, f'part{p:04d}{ext}') for ext in ('.npy', '.json', '.leaves.jsonl.gz')}
    if not all(os.path.exists(v) for v in files.values()):
        bad.append((p, 'missing')); continue
    meta = json.load(open(files['.json']))
    if any(meta[k] != first[k] for k in keys) or int(meta['part']) != p:
        bad.append((p, 'header mismatch')); continue
    sh = {ext: hashlib.sha256(open(v, 'rb').read()).hexdigest() for ext, v in files.items()}
    ok = [r for r in logs.get(p, []) if r.get('sha256') == sh and r.get('fails') == 0]
    if not ok:
        bad.append((p, 'no passing check log for these bytes')); continue
    leaves += ok[0]['leaves']
    m = ok[0]['min_margin']
    minm = m if minm is None else min(minm, m)
print(json.dumps(dict(nparts=NP, all_ok=(len(bad) == 0), leaves=leaves, min_margin=minm, bad=bad[:20], nbad=len(bad),
                      tau=first['tau'], family=first['family'])))
