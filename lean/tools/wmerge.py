#!/usr/bin/env python3
"""Merge the per-range outputs of tools/wconvert.py into one data tree for the Lean checker.

Input: CONV/rNNN = `wconvert.py CERT CONV/rNNN --parts A:B` for the ranges [A, B) = [R*NNN, R*NNN + R) (R parts each).
Output (DATA):
  skel/sNNNNN.txt     the skeletons of all parts
  chunks/cNNNNN.txt   the chunks of all ranges, renumbered consecutively in range order (so that sorting the names gives
                      every (p, u) in part order, u ascending)
  manifest.json       counts, provenance, per chunk its units and leaves, and the sha256 of every file
  SHA256SUMS          the same hashes in `sha256sum -c` format
Checks: every part has a skeleton; the chunks list every unit (p, u), u = 0 .. (number of 'U' in the skeleton) - 1, in
order; the records of every chunk match its codes and its manifest entry; the total number of leaves.

usage: python3 -I -B wmerge.py CERT CONV DATA [--range-size R] [--nparts N] [--expect-leaves L] [--source-name S] [--move]
"""
import argparse
import hashlib
import json
import os
import shutil


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        while True:
            b = f.read(1 << 22)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def scan_chunk(text):
    """the units [(p, u)] of a chunk text and its number of leaves; checks the block structure"""
    toks = text.split(' ')
    assert toks[0][0] == 'T'
    n = int(toks[0][1:])
    i = n + 1
    units = []
    leaves = 0
    while i < len(toks):
        t = toks[i]
        assert t[0] == 'U', (i, t[:20])
        p, u = (int(x) for x in t[1:].split('.'))
        c = toks[i + 1]
        assert c[0] == 'C'
        nl = c.count('L') + c.count('K')
        assert i + 2 + nl <= len(toks)
        units.append((p, u))
        leaves += nl
        i += 2 + nl
    assert i == len(toks)
    return units, leaves


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('conv')
    ap.add_argument('data')
    ap.add_argument('--range-size', type=int, default=64)
    ap.add_argument('--nparts', type=int, default=16384)
    ap.add_argument('--expect-leaves', type=int, default=189594732)
    ap.add_argument('--source-name', default='cert_w2400a')
    ap.add_argument('--move', action='store_true', help='move the files instead of copying them')
    a = ap.parse_args()
    R = a.range_size
    nranges = (a.nparts + R - 1) // R
    os.makedirs(os.path.join(a.data, 'skel'), exist_ok=True)
    os.makedirs(os.path.join(a.data, 'chunks'), exist_ok=True)
    put = shutil.move if a.move else shutil.copyfile
    chunks = []
    nunits_part = []
    for k in range(nranges):
        rdir = os.path.join(a.conv, f'r{k:03d}')
        p0, p1 = k * R, min(a.nparts, (k + 1) * R)
        man = sorted(json.load(open(os.path.join(rdir, 'manifest.json'))), key=lambda e: e['chunk'])
        assert [e['chunk'] for e in man] == list(range(len(man)))
        for p in range(p0, p1):
            src = os.path.join(rdir, 'skel', f's{p:05d}.txt')
            dst = os.path.join(a.data, 'skel', f's{p:05d}.txt')
            put(src, dst)
            s = open(dst).read()
            assert s and set(s) <= set('0123456789abU'), p
            nunits_part.append(s.count('U'))
        for e in man:
            name = f'c{len(chunks):05d}'
            src = os.path.join(rdir, 'chunks', f'c{e["chunk"]:05d}.txt')
            dst = os.path.join(a.data, 'chunks', f'{name}.txt')
            put(src, dst)
            text = open(dst).read()
            assert len(text.encode()) == e['bytes'], name
            units, leaves = scan_chunk(text)
            assert units == [tuple(x) for x in e['units']], name
            assert leaves == e['leaves'], name
            assert all(p0 <= p < p1 for p, _ in units), name
            chunks.append(dict(name=name, units=[list(x) for x in units], leaves=leaves, bytes=e['bytes'], range=k))
        print(f'range {k} parts {p0}:{p1} chunks {len(man)} total chunks {len(chunks)}', flush=True)
    # the chunks list every unit in order
    seq = [tuple(x) for c in chunks for x in c['units']]
    expect = [(p, u) for p in range(a.nparts) for u in range(nunits_part[p])]
    assert seq == expect, 'unit sequence differs from the skeletons'
    total = sum(c['leaves'] for c in chunks)
    assert total == a.expect_leaves, (total, a.expect_leaves)
    files = {}
    for p in range(a.nparts):
        rel = f'skel/s{p:05d}.txt'
        files[rel] = sha256_file(os.path.join(a.data, rel))
    for c in chunks:
        rel = f'chunks/{c["name"]}.txt'
        c['sha256'] = files[rel] = sha256_file(os.path.join(a.data, rel))
    here = os.path.dirname(os.path.abspath(__file__))
    manifest = dict(
        format='worm-data-1 (WormCore/FORMAT.md)',
        source=dict(name=a.source_name, sha256_of_SHA256SUMS=sha256_file(os.path.join(a.cert, 'SHA256SUMS'))),
        produced_by=dict(
            converter=dict(file='tools/wconvert.py', sha256=sha256_file(os.path.join(here, 'wconvert.py')),
                           args='CERT CONV/rNNN --parts A:B (defaults --unit 50000 --chunk 50000)'),
            merge=dict(file='tools/wmerge.py', sha256=sha256_file(os.path.abspath(__file__)),
                       args=f'--range-size {R} --nparts {a.nparts} --expect-leaves {a.expect_leaves} --source-name {a.source_name}'),
            ranges=f'[{R}*k, {R}*k + {R}) for k = 0..{nranges - 1}; chunks renumbered consecutively in range order'),
        counts=dict(parts=a.nparts, units=len(seq), leaves=total, chunks=len(chunks),
                    bytes=sum(c['bytes'] for c in chunks) + sum(os.path.getsize(os.path.join(a.data, f'skel/s{p:05d}.txt'))
                                                             for p in range(a.nparts))),
        chunks=chunks,
        files=files)
    with open(os.path.join(a.data, 'manifest.json'), 'w') as f:
        json.dump(manifest, f, indent=None, separators=(',', ':'))
    with open(os.path.join(a.data, 'SHA256SUMS'), 'w') as f:
        f.write(f'{sha256_file(os.path.join(a.data, "manifest.json"))}  ./manifest.json\n')
        for rel in sorted(files):
            f.write(f'{files[rel]}  ./{rel}\n')
    print('counts', json.dumps(manifest['counts']))


if __name__ == '__main__':
    main()
