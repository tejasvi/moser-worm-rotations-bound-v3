#!/usr/bin/env python3
"""Assemble a part from its per-cell runs (wsearch.py ... --cell k, files in OUTDIR/cells/): codes and leaf records are
concatenated in cell order (the DFS of a part processes its cells in that order, each independently), the header gets
summed counts.  Temporary files end in .tmp and are renamed into place (json last).
  assemble.py OUTDIR PART NCELLS     exit 0: assembled or the part exists already; exit 1: a cell is missing"""
import sys, os, json, gzip
import numpy as np
out, part, ncells = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
stem = os.path.join(out, f'part{part:04d}')
if os.path.exists(stem + '.json'):
    sys.exit(0)
cd = os.path.join(out, 'cells')
names = [os.path.join(cd, f'part{part:04d}.c{k:02d}') for k in range(ncells)]
if not all(os.path.exists(n + '.json') for n in names):
    sys.exit(1)
metas = [json.load(open(n + '.json')) for n in names]
assert all(m['cell_index'] == k and m['part'] == part for k, m in enumerate(metas))
codes = np.concatenate([np.load(n + '.npy') for n in names])
with open(stem + '.npy.tmp', 'wb') as f:
    np.save(f, codes)
with gzip.open(stem + '.leaves.jsonl.gz.tmp', 'wt') as f:
    for n in names:
        with gzip.open(n + '.leaves.jsonl.gz', 'rt') as g:
            for line in g:
                f.write(line)
meta = dict(metas[0]); del meta['cell_index']
for k in ('boxes', 'leaves', 'lemmaK', 'secs'):
    meta[k] = sum(m[k] for m in metas)
meta['minL'] = min(m['minL'] for m in metas)
meta['assembled_from_cells'] = ncells
with open(stem + '.json.tmp', 'w') as f:
    json.dump(meta, f)
os.rename(stem + '.npy.tmp', stem + '.npy')
os.rename(stem + '.leaves.jsonl.gz.tmp', stem + '.leaves.jsonl.gz')
os.rename(stem + '.json.tmp', stem + '.json')
print('assembled', part)
