#!/usr/bin/env python3
"""
Extract all Lean 4 declaration positions from lean/CombUnipotent/*.lean.

Tracks `namespace` / `end` to recover fully-qualified names.

Produces a JSON file mapping declaration name to {file, line} info, used by
the blueprint's find/ redirect page to go straight to the source.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


# Allow optional attribute block / modifier prefix, then the declaration keyword.
DECL_RE = re.compile(
    r"""^\s*
        (?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*
        (?P<kw>theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque)\s+
        (?P<name>[\w\.]+)
    """,
    re.VERBOSE,
)

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w\.]+)")
END_RE = re.compile(r"^\s*end(?:\s+([\w\.]+))?\s*$")
SECTION_OPEN_RE = re.compile(r"^\s*section\b")
SECTION_CLOSE_RE = re.compile(r"^\s*end\s*$")


def extract_from_file(path: Path, repo_root: Path) -> list[dict]:
    rows: list[dict] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except Exception:
        return rows
    rel = path.relative_to(repo_root).as_posix()

    ns_stack: list[str] = []  # each entry is a single namespace segment

    for i, line in enumerate(lines, start=1):
        m_ns = NAMESPACE_RE.match(line)
        if m_ns:
            # A `namespace A.B` introduces two nested segments.
            for seg in m_ns.group(1).split("."):
                ns_stack.append(seg)
            continue
        m_end = END_RE.match(line)
        if m_end:
            tail = m_end.group(1)
            if tail:
                # `end A.B` — pop matching segments.
                parts = tail.split(".")
                for _ in parts:
                    if ns_stack:
                        ns_stack.pop()
            else:
                # bare `end` — pop one (closes either a namespace or a section).
                if ns_stack:
                    ns_stack.pop()
            continue

        m = DECL_RE.match(line)
        if not m:
            continue
        name = m.group("name")
        if not name:
            continue

        # Fully qualified: join namespace stack + name, but only if the name
        # doesn't already start with one of the namespace segments (e.g., when
        # the user wrote `def NS.X ...` inside `namespace NS`).
        if "." in name:
            # Already qualified — use as is.
            full = name
        else:
            full = ".".join(ns_stack + [name]) if ns_stack else name

        rows.append({"name": full, "file": rel, "line": i})

    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True, help="Lean source root (e.g., lean/CombUnipotent)")
    ap.add_argument("--repo-root", default=".", help="Repository root (for relative paths)")
    ap.add_argument("--out", required=True, help="Output JSON path")
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()
    root = Path(args.root).resolve()

    rows: list[dict] = []
    for p in sorted(root.rglob("*.lean")):
        rows.extend(extract_from_file(p, repo_root))

    seen: dict[str, dict] = {}
    duplicates: dict[str, int] = {}
    for row in rows:
        name = row["name"]
        if name not in seen:
            seen[name] = row
        else:
            duplicates[name] = duplicates.get(name, 1) + 1

    # Also index by the short name (last dotted segment) — but only when the
    # short name is unambiguous across all fully-qualified names. This lets
    # blueprints reference either `prop_11_8` or `BMSZ.prop_11_8`.
    short_counts: dict[str, list[str]] = {}
    for full in seen:
        short = full.split(".")[-1]
        short_counts.setdefault(short, []).append(full)
    alias_count = 0
    for short, fulls in short_counts.items():
        if len(fulls) == 1 and short not in seen:
            seen[short] = seen[fulls[0]]
            alias_count += 1

    out = {
        "generated_by": "tools/extract_lean_decls.py",
        "count": len(seen),
        "duplicates_dropped": len(duplicates),
        "short_aliases_added": alias_count,
        "decls": seen,
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2))
    print(f"[extract_lean_decls] wrote {len(seen)} decls to {out_path}")
    if duplicates:
        top = sorted(duplicates.items(), key=lambda x: -x[1])[:5]
        print(f"[extract_lean_decls] dropped {len(duplicates)} duplicates, top: {top}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
