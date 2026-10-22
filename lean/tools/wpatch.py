#!/usr/bin/env python3
"""Apply leaf patches found by tools/wpatch_probe.lean to the worm data (data/).

A patch replaces the code of one failing leaf ('L' or 'K') of a unit by a subdivision of its box (exact midpoint
splits, DFS preorder, e.g. `0LL`), with the leaf's record token repeated once per new leaf. The data is untrusted:
the checker re-verifies every piece; the unit lists do not change.

For each patch line (JSON from the probe; `code_after` must be set and every `ok_after` true) this script checks the
unit, leaf letter and record token at the leaf position, rewrites the chunk text, re-scans it (same units, leaves +
extra), and updates data/manifest.json (chunk leaves, bytes and sha256, `leaves_converted`, counts, a `patches` list
with codes and margins before and after) and data/SHA256SUMS.

usage: python3 -I -B wpatch.py DATADIR PATCHES.jsonl
"""
import hashlib
import json
import os
import sys


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''):
            h.update(b)
    return h.hexdigest()


def scan(text):
    """units [(p, u)] and number of leaves of a chunk text"""
    toks = text.split(' ')
    n = int(toks[0][1:])
    i = n + 1
    units = []
    leaves = 0
    while i < len(toks):
        p, u = (int(x) for x in toks[i][1:].split('.'))
        nl = toks[i + 1].count('L') + toks[i + 1].count('K')
        units.append((p, u))
        leaves += nl
        i += 2 + nl
    assert i == len(toks)
    return units, leaves


def apply_patch(text, pt):
    toks = text.split(' ')
    n = int(toks[0][1:])
    i = n + 1
    while i < len(toks):
        head = toks[i]
        codes = toks[i + 1]
        nl = codes.count('L') + codes.count('K')
        if head == 'U' + pt['unit']:
            j = pt['leaf']
            assert 0 <= j < nl, (pt, nl)
            pos = [q for q, ch in enumerate(codes) if ch in 'LK'][j]
            letter = codes[pos]
            assert letter == pt['letter'] == pt['code_before'], (letter, pt)
            assert toks[i + 2 + j] == pt['record'], (toks[i + 2 + j], pt)
            new = pt['code_after']
            assert set(new) <= set('0123456789ab' + letter) and new[-1] == letter
            k = new.count(letter)
            assert k == pt['extra_leaves'] + 1 and k == len(pt['ok_after']) and all(pt['ok_after'])
            toks[i + 1] = codes[:pos] + new + codes[pos + 1:]
            toks[i + 2 + j:i + 3 + j] = [pt['record']] * k
            return ' '.join(toks)
        i += 2 + nl
    raise AssertionError(f'unit {pt["unit"]} not in chunk {pt["chunk"]}')


def main():
    data, pfile = sys.argv[1], sys.argv[2]
    patches = [json.loads(l) for l in open(pfile) if l.strip()]
    assert all(p.get('code_after') for p in patches), 'a leaf without a fix: stop'
    man_path = os.path.join(data, 'manifest.json')
    man = json.load(open(man_path))
    by_name = {c['name']: c for c in man['chunks']}
    here = os.path.dirname(os.path.abspath(__file__))
    done = man.setdefault('patches', [])
    seen = {(p['chunk'], p['unit'], p['leaf_converted']) for p in done}
    # within a unit, apply from the highest leaf index down, so that earlier indices stay valid
    for pt in sorted(patches, key=lambda p: (p['chunk'], p['unit'], -p['leaf'])):
        key = (pt['chunk'], pt['unit'], pt['leaf'])
        assert key not in seen, f'already applied: {key}'
        c = by_name[pt['chunk']]
        path = os.path.join(data, 'chunks', pt['chunk'] + '.txt')
        old = open(path).read()
        units0, leaves0 = scan(old)
        assert leaves0 == c['leaves'] and [list(x) for x in units0] == c['units']
        new = apply_patch(old, pt)
        units1, leaves1 = scan(new)
        assert units1 == units0 and leaves1 == leaves0 + pt['extra_leaves']
        tmp = path + '.tmp'
        open(tmp, 'w').write(new)
        os.replace(tmp, path)
        c.setdefault('leaves_converted', leaves0)
        c['leaves'] = leaves1
        c['bytes'] = len(new.encode())
        c['sha256'] = sha256_file(path)
        man['files'][f'chunks/{pt["chunk"]}.txt'] = c['sha256']
        done.append(dict(chunk=pt['chunk'], unit=pt['unit'], leaf_converted=pt['leaf'], letter=pt['letter'],
                         record=pt['record'], code_before=pt['code_before'], code_after=pt['code_after'],
                         extra_leaves=pt['extra_leaves'], margin_before=pt['margin_before'],
                         margin_before_real=pt['margin_before'] / 2 ** 56, margins_after=pt['margins_after'],
                         margins_after_real=[m / 2 ** 56 for m in pt['margins_after']], leafOKR6_after=pt['ok_after']))
        print(f'patched {pt["chunk"]} unit {pt["unit"]} leaf {pt["leaf"]}: {pt["code_before"]} -> {pt["code_after"]}, '
              f'leaves {leaves0} -> {leaves1}')
    counts = man['counts']
    counts.setdefault('leaves_converted', counts['leaves'])
    counts['leaves'] = sum(c['leaves'] for c in man['chunks'])
    counts['extra_leaves_from_patches'] = counts['leaves'] - counts['leaves_converted']
    counts['bytes'] = sum(c['bytes'] for c in man['chunks']) + sum(
        os.path.getsize(os.path.join(data, rel)) for rel in man['files'] if rel.startswith('skel/'))
    man['produced_by']['patch'] = dict(
        file='tools/wpatch.py', sha256=sha256_file(os.path.abspath(__file__)),
        probe=dict(file='tools/wpatch_probe.lean', sha256=sha256_file(os.path.join(here, 'wpatch_probe.lean')),
                   rule='failing leaves of leafOKR famW maxsmallW tauHiW rdepthW; exact midpoint splits; record repeated'))
    tmp = man_path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(man, f, indent=None, separators=(',', ':'))
    os.replace(tmp, man_path)
    with open(os.path.join(data, 'SHA256SUMS.tmp'), 'w') as f:
        f.write(f'{sha256_file(man_path)}  ./manifest.json\n')
        for rel in sorted(man['files']):
            f.write(f'{man["files"][rel]}  ./{rel}\n')
    os.replace(os.path.join(data, 'SHA256SUMS.tmp'), os.path.join(data, 'SHA256SUMS'))
    print('counts', json.dumps(counts))


if __name__ == '__main__':
    main()
