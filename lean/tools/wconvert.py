#!/usr/bin/env python3
"""Convert the frozen worm certificate (cert_w2400a) into the data of the Lean checker (WormCore.Data):

  skeletons   per part: the DFS codes from the 64 root cells down to the units ('0'-'9', 'a', 'b' split a coordinate,
              lower half first; 'U' a unit: a subtree with at most UNIT leaves, checked in a chunk);
  chunks      groups of consecutive units (all parts in order) with about CHUNK leaves; per unit the codes of its
              subtree ('L' a leaf with one structure, 'K' a Lemma K leaf) and its leaf records, plus a structure table
              per chunk.

Text format of a chunk (tokens separated by single spaces):
  T<n> then n structure tokens:  s<ids> | f<ids>|<zx>|<zy> | c<ids>|<tree>
        ids: one letter per global vertex ('a' + id); zx, zy: fan centre mantissas at 2^-56 (decimal);
        tree: 's' | 'f'<r> | 'c'<s><t><left><right>, with r, s, t one character each ('0'-'9', 'a'-'z').
  U<part>.<unit> then C<codes> then one record token per leaf of the unit:
        <i>              one structure (table index, base 36), weight 1
        <i>,<w>;<i>,<w>  Lemma K: table indices and weights (mantissas at 2^-56, exact floors, sum <= 2^56)

The data is not trusted: the checker recomputes every box from the root cells and re-verifies every leaf.
usage: python3 -B wconvert.py CERTDIR OUTDIR [--parts A:B] [--unit N] [--chunk N]"""
import sys, os, json, gzip, argparse
from fractions import Fraction as Fr
import numpy as np

DS = 56
CODE = '0123456789ab'
B36 = '0123456789abcdefghijklmnopqrstuvwxyz'


def b36(n):
    assert n >= 0
    s = ''
    while True:
        s = B36[n % 36] + s
        n //= 36
        if n == 0:
            return s


def ch36(n):
    assert 0 <= n < 36
    return B36[n]


def tree_str(t):
    if t[0] == 's':
        return 's'
    if t[0] == 'f':
        return 'f' + ch36(int(t[1]))
    return 'c' + ch36(int(t[1])) + ch36(int(t[2])) + tree_str(t[3]) + tree_str(t[4])


def struct_str(s):
    ids = ''.join(chr(ord('a') + int(v)) for v in s['v'])
    if s['m'] == 'small':
        return 's' + ids
    if s['m'] == 'fan':
        zx = round(s['z'][0] * (1 << DS)); zy = round(s['z'][1] * (1 << DS))
        return f'f{ids}|{zx}|{zy}'
    return f'c{ids}|{tree_str(s["t"])}'


def convert_part(certdir, part, unit):
    """skeleton string and units [(subtree codes, leaf records)] of one part, in DFS order."""
    codes = [int(x) for x in np.load(os.path.join(certdir, f'part{part:04d}.npy'))]
    recs = gzip.open(os.path.join(certdir, f'part{part:04d}.leaves.jsonl.gz'), 'rt')
    n = len(codes); end = [0] * n; size = [0] * n; st = []
    for i in range(n - 1, -1, -1):              # reverse pass: subtree ends and leaf counts
        if codes[i] in (253, 254):
            end[i] = i + 1; size[i] = 1; st.append(i)
        else:
            assert 0 <= codes[i] < 12
            a = st.pop(); b = st.pop()           # lower child at i + 1, upper child after it
            assert a == i + 1 and b == end[a]
            end[i] = end[b]; size[i] = size[a] + size[b]; st.append(i)
    roots = st[::-1]                             # the root cells, in order
    assert roots[0] == 0 and all(end[roots[k]] == roots[k + 1] for k in range(len(roots) - 1)) and end[roots[-1]] == n
    skel = []; units = []

    def emit(i):
        if size[i] <= unit:
            sub = ''.join('L' if x == 254 else 'K' if x == 253 else CODE[x] for x in codes[i:end[i]])
            rl = [json.loads(recs.readline()) for _ in range(size[i])]
            units.append((sub, rl)); skel.append('U')
        else:
            skel.append(CODE[codes[i]])
            emit(i + 1); emit(end[i + 1])

    for r in roots:
        emit(r)
    assert recs.readline() == ''
    return ''.join(skel), units, len(roots)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certdir'); ap.add_argument('outdir')
    ap.add_argument('--parts', default='0:16384'); ap.add_argument('--unit', type=int, default=50000)
    ap.add_argument('--chunk', type=int, default=50000)
    a = ap.parse_args()
    p0, p1 = (int(x) for x in a.parts.split(':'))
    os.makedirs(os.path.join(a.outdir, 'skel'), exist_ok=True)
    os.makedirs(os.path.join(a.outdir, 'chunks'), exist_ok=True)
    chunk = []; cleaves = 0; cid = 0; manifest = []

    def flush():
        nonlocal chunk, cleaves, cid
        if not chunk:
            return
        table = {}; toks = []
        for part, ui, sub, rl in chunk:
            toks.append(f'U{part}.{ui}'); toks.append('C' + sub)
            for r in rl:
                ws = [Fr(x) for x in r['w']]; tot = sum(ws)
                items = []
                for s_, w in zip(r['S'], ws):
                    k = struct_str(s_)
                    if k not in table:
                        table[k] = len(table)
                    items.append((table[k], int(w * (1 << DS) / tot)))
                if len(items) == 1:
                    toks.append(b36(items[0][0]))
                else:
                    toks.append(';'.join(f'{b36(i)},{w}' for i, w in items))
        tab = [None] * len(table)
        for k, i in table.items():
            tab[i] = k
        text = ' '.join([f'T{len(tab)}'] + tab + toks)
        open(os.path.join(a.outdir, 'chunks', f'c{cid:05d}.txt'), 'w').write(text)
        manifest.append(dict(chunk=cid, units=[(p, u) for p, u, _, _ in chunk], leaves=cleaves, bytes=len(text)))
        cid += 1; chunk = []; cleaves = 0

    for part in range(p0, p1):
        skel, units, ncells = convert_part(a.certdir, part, a.unit)
        assert ncells == 64
        open(os.path.join(a.outdir, 'skel', f's{part:05d}.txt'), 'w').write(skel)
        for ui, (sub, rl) in enumerate(units):
            if cleaves + len(rl) > a.chunk and chunk:
                flush()
            chunk.append((part, ui, sub, rl)); cleaves += len(rl)
    flush()
    json.dump(manifest, open(os.path.join(a.outdir, 'manifest.json'), 'w'))
    print('parts', p1 - p0, 'chunks', cid, 'bytes', sum(m['bytes'] for m in manifest))


if __name__ == '__main__':
    main()
