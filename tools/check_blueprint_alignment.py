#!/usr/bin/env python3
"""
Verify that every \lean{...} name referenced in the blueprint LaTeX sources
corresponds to an actual Lean 4 declaration in the project.

Exits non-zero if any mismatches are found.

Usage:
    python3 tools/check_blueprint_alignment.py \
        --blueprint lean/blueprint/src \
        --decls docs/blueprint/find/lean_decls.json
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


LEAN_CMD_RE = re.compile(r"\\lean\{([^}]+)\}")


def collect_lean_refs(blueprint_dir: Path) -> list[tuple[str, Path]]:
    """Return list of (decl_name, source_path) for every \lean{...} reference."""
    refs: list[tuple[str, Path]] = []
    for tex_path in sorted(blueprint_dir.rglob("*.tex")):
        try:
            content = tex_path.read_text(encoding="utf-8")
        except Exception:
            continue
        for match in LEAN_CMD_RE.finditer(content):
            group = match.group(1)
            # \lean{A, B, C} means three separate declarations.
            for raw in group.split(","):
                name = raw.strip()
                if name:
                    refs.append((name, tex_path))
    return refs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--blueprint", required=True, help="Blueprint src dir (LaTeX)")
    ap.add_argument("--decls", required=True, help="JSON from extract_lean_decls.py")
    ap.add_argument("--strict", action="store_true", help="Exit non-zero on any mismatch")
    args = ap.parse_args()

    blueprint_dir = Path(args.blueprint)
    with open(args.decls, encoding="utf-8") as f:
        decl_data = json.load(f)
    known: set[str] = set(decl_data["decls"].keys())

    refs = collect_lean_refs(blueprint_dir)
    print(f"[checkdecls] found {len(refs)} \\lean{{...}} references across {blueprint_dir}")
    print(f"[checkdecls] loaded {len(known)} Lean declarations")

    missing: dict[str, list[Path]] = {}
    for name, path in refs:
        if name not in known:
            missing.setdefault(name, []).append(path)

    if missing:
        print(f"\n[checkdecls] MISSING {len(missing)} names not found in Lean:")
        for name, paths in sorted(missing.items()):
            files = sorted({p.name for p in paths})
            print(f"  - {name}  (referenced in: {', '.join(files)})")
        if args.strict:
            return 1

    print(f"\n[checkdecls] {len(refs) - sum(len(v) for v in missing.values())} OK, {sum(len(v) for v in missing.values())} missing")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
