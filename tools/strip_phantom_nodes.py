#!/usr/bin/env python3
"""
Strip plastex-generated phantom nodes (id matching aXXXXXXX) from the
dep_graph_document.html file.

These phantoms come from a plasTeX parser quirk that creates empty
definition_thmwrapper / lemma_thmwrapper divs around \begin{cases} display
math inside theorem environments. They have no real content and pollute
the dependency graph.

Usage:
    python3 tools/strip_phantom_nodes.py <path_to_dep_graph_document.html>
"""
import re
import sys
from pathlib import Path


def strip(html: str) -> tuple[str, int]:
    # Remove the inline graphviz `dot` source — nodes referenced by phantom IDs.
    # Pattern: a0000000NN [color=...,...,shape=...]; possibly with edges
    phantom_pat = re.compile(r'a0000000\d+')

    # Find all phantom IDs first
    phantoms = sorted(set(phantom_pat.findall(html)))
    if not phantoms:
        return html, 0

    out = html
    removed = 0

    # 1) Remove phantom node declarations from the digraph string
    #    e.g.  a0000000065 [color=blue, fillcolor=...]
    for pid in phantoms:
        # Match `pid [...]` (node decl) — within graphviz dot text
        decl_pat = re.compile(rf'\b{re.escape(pid)}\s+\[[^\]]*\]\s*;?', re.MULTILINE)
        n = len(decl_pat.findall(out))
        out = decl_pat.sub('', out)
        removed += n

    # 2) Remove phantom modal containers (the off-screen divs)
    for pid in phantoms:
        # Match the entire <div ... id="pid_modal">...</div> block (greedy until matching close)
        # Easier: regex the modal-container with class hint
        modal_pat = re.compile(
            rf'<div class="modal-container"[^>]*\bid="{re.escape(pid)}_modal"[\s\S]*?</div>\s*</div>\s*</div>',
            re.IGNORECASE,
        )
        out = modal_pat.sub('', out)

        # Also remove <div class="thm" id="pid" style="display: none">...</div>
        thm_pat = re.compile(
            rf'<div class="thm" id="{re.escape(pid)}"[\s\S]*?</div>\s*</div>\s*</div>\s*</div>',
            re.IGNORECASE,
        )
        out = thm_pat.sub('', out)

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
        print(f'[strip_phantom_nodes] removed {count} phantom node declarations from {p}')
    else:
        print(f'[strip_phantom_nodes] no phantom nodes in {p}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
