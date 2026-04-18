#!/usr/bin/env python3
"""
Extract programmatic dependency graph from Lean source.

For each theorem/lemma in lean/CombUnipotent/, parse the proof body and
extract identifiers that match other declared theorem names. Output a JSON
mapping: theorem_name → [list of dependencies].

Then cross-reference with blueprint `\\lean{...}` annotations to derive a
label-level dependency graph that can be compared against the blueprint's
manually-written `\\uses{...}` directives.

Usage:
    python3 tools/extract_lean_deps.py \\
        --decls docs/blueprint/find/lean_decls.json \\
        --blueprint lean/blueprint/src/chapters \\
        --out lean_deps.json
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

# ----------------------------------------------------------------------------
# Lean source parsing
# ----------------------------------------------------------------------------

# Identifier pattern (allowing dots, underscores, primes, digits, unicode)
IDENT_RE = re.compile(r'\b([A-Za-z_][A-Za-z_0-9.\u0370-\u1FFF\u2070-\uFFFF]*)\b')

# Pattern that opens a theorem/def block. We capture the body up to the next
# top-level declaration.
DECL_OPEN_RE = re.compile(
    r'^(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*'
    r'(?:theorem|lemma|def|abbrev|instance)\s+([\w\.]+)',
    re.MULTILINE,
)


def split_into_decl_bodies(text: str) -> list[tuple[str, str]]:
    """Return a list of (decl_name, body_text) for each theorem/lemma/def."""
    matches = list(DECL_OPEN_RE.finditer(text))
    bodies: list[tuple[str, str]] = []
    for i, m in enumerate(matches):
        name = m.group(1)
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        bodies.append((name, text[start:end]))
    return bodies


def extract_referenced_idents(body: str) -> set[str]:
    """Extract all identifiers in a decl body. Excludes string literals and
    comments."""
    # Strip line comments (-- ...)
    body = re.sub(r'--[^\n]*', '', body)
    # Strip block comments (/- ... -/)
    body = re.sub(r'/-.*?-/', '', body, flags=re.DOTALL)
    # Strip string literals (rough)
    body = re.sub(r'"[^"]*"', '', body)
    # Strip the `theorem name (args) :` header — proof body is what we want.
    # Find first `:= ` and only keep what follows (the proof / def body).
    if ':=' in body:
        body = body.split(':=', 1)[1]
    return set(IDENT_RE.findall(body))


# ----------------------------------------------------------------------------
# Build dependency graph
# ----------------------------------------------------------------------------

def build_lean_dep_graph(repo: Path, decls: dict) -> dict[str, list[str]]:
    """For each known declaration, list which other known declarations it
    references in its proof / definition body."""
    # Index decls by short name (last segment) for fast lookup.
    short_to_full: dict[str, list[str]] = {}
    for full_name in decls:
        short_to_full.setdefault(full_name.split('.')[-1], []).append(full_name)
    full_names = set(decls.keys())

    deps: dict[str, list[str]] = {}
    for full_name, info in decls.items():
        path = repo / info['file']
        try:
            text = path.read_text(encoding='utf-8')
        except Exception:
            continue
        for d_name, body in split_into_decl_bodies(text):
            if d_name != full_name and not full_name.endswith(f'.{d_name}'):
                # only the matching decl
                if d_name == full_name.split('.')[-1] and d_name in short_to_full \
                        and full_name in short_to_full[d_name]:
                    pass
                else:
                    continue
            idents = extract_referenced_idents(body)
            referenced: set[str] = set()
            for tok in idents:
                # Match by short name OR fully qualified
                if tok in full_names:
                    referenced.add(tok)
                elif tok in short_to_full and len(short_to_full[tok]) == 1:
                    referenced.add(short_to_full[tok][0])
            referenced.discard(full_name)
            deps[full_name] = sorted(referenced)
            break  # only process the matching decl in this file

    return deps


# ----------------------------------------------------------------------------
# Map to blueprint label graph
# ----------------------------------------------------------------------------

LEAN_REF_RE = re.compile(r'\\lean\{([^}]+)\}')
LABEL_RE = re.compile(r'\\label\{([^}]+)\}')
USES_RE = re.compile(r'\\uses\{([^}]+)\}')
ENV_OPEN_RE = re.compile(r'\\begin\{(lemma|proposition|theorem|corollary|definition)\}', )


def parse_blueprint(chapters: Path) -> tuple[dict[str, list[str]], dict[str, set[str]]]:
    """Return:
       - lean_to_label: each Lean name → blueprint label that references it
       - label_uses:    each blueprint label → declared \\uses{...} set"""
    lean_to_label: dict[str, list[str]] = {}
    label_uses: dict[str, set[str]] = {}
    for tex in chapters.glob('*.tex'):
        text = tex.read_text()
        # Iterate environment blocks
        for m in re.finditer(
            r'\\begin\{(lemma|proposition|theorem|corollary|definition)\}.*?\\end\{\1\}',
            text, re.DOTALL,
        ):
            block = m.group(0)
            label_m = LABEL_RE.search(block)
            if not label_m:
                continue
            label = label_m.group(1)
            for lm in LEAN_REF_RE.finditer(block):
                for n in lm.group(1).split(','):
                    lean_to_label.setdefault(n.strip(), []).append(label)
            uses: set[str] = set()
            for um in USES_RE.finditer(block):
                for u in um.group(1).split(','):
                    uses.add(u.strip())
            label_uses.setdefault(label, set()).update(uses)
    return lean_to_label, label_uses


def derive_label_deps(lean_deps: dict, lean_to_label: dict) -> dict[str, set[str]]:
    """For each blueprint label, derive the set of OTHER labels it depends on
    based on the Lean dependency graph + lean→label mapping."""
    label_deps: dict[str, set[str]] = {}
    for lean_name, lean_refs in lean_deps.items():
        labels = lean_to_label.get(lean_name, [])
        for label in labels:
            for ref_lean in lean_refs:
                ref_labels = lean_to_label.get(ref_lean, [])
                for r in ref_labels:
                    if r != label:
                        label_deps.setdefault(label, set()).add(r)
    return label_deps


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--decls', required=True)
    ap.add_argument('--blueprint', required=True, help='blueprint chapters dir')
    ap.add_argument('--out', required=True, help='output JSON')
    ap.add_argument('--repo-root', default='.')
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    with open(args.decls, encoding='utf-8') as f:
        decls = json.load(f)['decls']

    print(f'[deps] indexing Lean decls: {len(decls)}')
    lean_deps = build_lean_dep_graph(repo, decls)
    print(f'[deps] extracted Lean dep graph for {len(lean_deps)} decls')

    lean_to_label, label_uses_declared = parse_blueprint(Path(args.blueprint))
    print(f'[deps] blueprint covers {len(lean_to_label)} Lean names → {len(label_uses_declared)} labels')

    label_deps_derived = derive_label_deps(lean_deps, lean_to_label)
    print(f'[deps] derived {len(label_deps_derived)} label-level dep sets from Lean')

    # Cross-check: declared `\uses` vs derived
    extra_declared, missing_declared = {}, {}
    for label, derived in label_deps_derived.items():
        declared = label_uses_declared.get(label, set())
        extra = declared - derived  # in \uses but not in Lean
        missing = derived - declared  # in Lean but not in \uses
        if extra:  extra_declared[label] = sorted(extra)
        if missing: missing_declared[label] = sorted(missing)

    out = {
        'lean_deps': lean_deps,
        'lean_to_label': lean_to_label,
        'label_deps_derived_from_lean': {k: sorted(v) for k, v in label_deps_derived.items()},
        'label_uses_declared_in_blueprint': {k: sorted(v) for k, v in label_uses_declared.items()},
        'extra_in_blueprint_uses_not_in_lean': extra_declared,
        'missing_in_blueprint_uses_present_in_lean': missing_declared,
    }
    Path(args.out).write_text(json.dumps(out, ensure_ascii=False, indent=2))
    print(f'[deps] wrote {args.out}')
    print()
    print(f'Audit summary:')
    print(f'  Labels with EXTRA \\uses (declared but not in Lean): {len(extra_declared)}')
    print(f'  Labels with MISSING \\uses (in Lean but not declared): {len(missing_declared)}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
