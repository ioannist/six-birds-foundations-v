#!/usr/bin/env python3
"""Validate the Foundations V imported-apparatus inventory.

Inventory paths are relative to a directory containing the Six Birds source
repositories. When all sources for a row are available, the audit also checks
its declared identifiers against those files. In a standalone checkout it
still validates the complete portable inventory; pass ``--require-sources``
to require the sibling source repositories.
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INVENTORY = ROOT / "formalization" / "inventory" / "imported_foundations.yml"
VALID_STATUSES = {"verified_correct", "corrected", "unresolved_needs_human"}


def _strip(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
        return value[1:-1]
    return value


def _load_with_yaml(path: Path) -> list[dict[str, Any]] | None:
    try:
        import yaml  # type: ignore[import-not-found]
    except Exception:
        return None

    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if isinstance(data, dict) and isinstance(data.get("entries"), list):
        return data["entries"]
    if isinstance(data, list):
        return data
    raise ValueError("inventory must be a list or a mapping with an 'entries' list")


def _load_minimal_yaml(path: Path) -> list[dict[str, Any]]:
    """Parse the small YAML subset used by imported_foundations.yml."""

    rows: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    active_list_key: str | None = None

    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        if raw.strip() == "entries:":
            continue

        stripped = raw.strip()
        if stripped.startswith("- "):
            if raw.startswith("  - "):
                if current is not None:
                    rows.append(current)
                current = {}
                active_list_key = None
                item = stripped[2:].strip()
                if not item:
                    continue
                if ":" not in item:
                    raise ValueError(f"{path}:{lineno}: expected key/value after list marker")
                key, value = item.split(":", 1)
                current[key.strip()] = _strip(value)
                continue
            if current is None or active_list_key is None:
                raise ValueError(f"{path}:{lineno}: nested list without active key")
            current.setdefault(active_list_key, []).append(_strip(stripped[2:]))
            continue

        if ":" not in stripped:
            raise ValueError(f"{path}:{lineno}: expected key/value line")
        if current is None:
            raise ValueError(f"{path}:{lineno}: key outside entry")
        key, value = stripped.split(":", 1)
        key = key.strip()
        value = value.strip()
        if value:
            current[key] = _strip(value)
            active_list_key = None
        else:
            current[key] = []
            active_list_key = key

    if current is not None:
        rows.append(current)
    return rows


def load_inventory(path: Path) -> list[dict[str, Any]]:
    rows = _load_with_yaml(path)
    if rows is not None:
        return rows
    return _load_minimal_yaml(path)


def identifiers_for(row: dict[str, Any]) -> list[str]:
    identifiers = row.get("identifiers", [])
    if isinstance(identifiers, str):
        return [identifiers]
    if isinstance(identifiers, list):
        return [str(item) for item in identifiers]
    return []


def source_paths_for(row: dict[str, Any]) -> list[Path]:
    source_paths = row.get("source_paths")
    if source_paths is None:
        source_path = row.get("source_path")
        return [Path(str(source_path))] if source_path else []
    if isinstance(source_paths, str):
        return [Path(source_paths)]
    if isinstance(source_paths, list):
        return [Path(str(item)) for item in source_paths]
    return []


def validate_row(
    row: dict[str, Any], corpus_root: Path, require_sources: bool
) -> tuple[list[str], bool]:
    errors: list[str] = []
    name = str(row.get("object_name", "<unnamed>"))

    for key in ("object_name", "exact_citation", "status"):
        if not row.get(key):
            errors.append(f"{name}: missing {key}")
    if not row.get("source_path") and not row.get("source_paths"):
        errors.append(f"{name}: missing source_path or source_paths")

    status = row.get("status")
    if status and status not in VALID_STATUSES:
        errors.append(f"{name}: invalid status {status!r}")

    source_paths = source_paths_for(row)
    if not source_paths:
        return errors, False

    absolute_paths = [path for path in source_paths if path.is_absolute()]
    for source_path in absolute_paths:
        errors.append(f"{name}: source path must be corpus-root-relative: {source_path}")
    if absolute_paths:
        return errors, False

    identifiers = identifiers_for(row)
    if not identifiers:
        errors.append(f"{name}: missing identifiers")

    resolved_paths = [corpus_root / path for path in source_paths]
    missing_paths = [
        source_path
        for source_path, resolved_path in zip(source_paths, resolved_paths)
        if not resolved_path.exists()
    ]
    if missing_paths:
        if require_sources:
            for source_path in missing_paths:
                errors.append(f"{name}: source path does not exist: {source_path}")
        return errors, False

    if not identifiers:
        return errors, True

    texts = {
        source_path: source_path.read_text(encoding="utf-8", errors="replace")
        for source_path in resolved_paths
    }
    for identifier in identifiers:
        if not any(identifier in text for text in texts.values()):
            paths = ", ".join(str(source_path) for source_path in texts)
            errors.append(f"{name}: identifier not found in any source path ({paths}): {identifier!r}")

    return errors, True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    parser.add_argument(
        "--corpus-root",
        type=Path,
        default=Path(os.environ.get("SIX_BIRDS_CORPUS_ROOT", ROOT.parent)),
        help="directory containing the Six Birds source repositories",
    )
    parser.add_argument(
        "--require-sources",
        action="store_true",
        help="fail unless every cited sibling source file is available",
    )
    args = parser.parse_args()

    if not args.inventory.exists():
        print(f"missing inventory: {args.inventory}", file=sys.stderr)
        return 2

    try:
        rows = load_inventory(args.inventory)
    except Exception as exc:
        print(f"failed to parse {args.inventory}: {exc}", file=sys.stderr)
        return 2

    errors: list[str] = []
    checked_sources = 0
    for row in rows:
        row_errors, sources_checked = validate_row(
            row, args.corpus_root, args.require_sources
        )
        errors.extend(row_errors)
        checked_sources += int(sources_checked)

    if errors:
        print("Foundations dependency audit failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    metadata_only = len(rows) - checked_sources
    print(
        "Foundations dependency audit passed: "
        f"{len(rows)} entries checked "
        f"({checked_sources} with source text, {metadata_only} metadata-only)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
