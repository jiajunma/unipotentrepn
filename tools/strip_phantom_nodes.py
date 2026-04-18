#!/usr/bin/env python3
"""
Strip plastex-generated phantom NODES from dep_graph_document.html.

A "phantom node" is one that appears as a NODE DECLARATION in the
embedded graphviz dot source (e.g. `aXXXXXXX [color=blue, ...]`) but has
no real semantic content (empty thm wrapper from a plasTeX parser quirk).

Important: only strip aXXXX IDs that appear as graph node declarations.
Many other aXXXX IDs are legitimate plasTeX-assigned IDs for displaymath,
list items, etc. — those must NOT be removed (they're the click targets).
"""
import re
import sys
from pathlib import Path


def strip(html: str) -> tuple[str, int]:
    # 1. Find IDs that appear as NODE DECLARATIONS in the dot source.
    #    These have form `aXXXXXXX [color=...,shape=...]` inside a renderDot string.
    node_decl_pat = re.compile(r'\b(a\d{8,})\s+\[color=\w+[^\]]*shape=(?:ellipse|box)[^\]]*\]')
    phantom_ids = sorted(set(node_decl_pat.findall(html)))

    if not phantom_ids:
        return html, 0

    out = html
    removed = 0

    # 2. For each phantom ID, remove its NODE DECLARATION from the dot source.
    for pid in phantom_ids:
        decl_pat = re.compile(rf'\b{re.escape(pid)}\s+\[[^\]]*\]\s*;?')
        n = len(decl_pat.findall(out))
        out = decl_pat.sub('', out)
        removed += n

        # Also remove edges referencing this id, e.g. "X -> pid" or "pid -> Y"
        edge_pat = re.compile(rf'\s*"?[^"]+"?\s*->\s*{re.escape(pid)}\s*\[[^\]]*\]\s*;?', re.MULTILINE)
        out = edge_pat.sub('', out)
        edge_pat2 = re.compile(rf'\s*{re.escape(pid)}\s*->\s*"?[^"]+"?\s*\[[^\]]*\]\s*;?', re.MULTILINE)
        out = edge_pat2.sub('', out)

    return out, removed


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: strip_phantom_nodes.py <html_file>", file=sys.stderr)
        return 1
    p = Path(sys.argv[1])
    html = p.read_text(encoding='utf-8')
    new, count = strip(html)
    if count:
        p.write_text(new, encoding='utf-8')
        print(f'[strip_phantom_nodes] removed {count} phantom node decl(s) from {p}')
    else:
        print(f'[strip_phantom_nodes] no phantom node decls in {p}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
