#!/usr/bin/env python3
"""r2-local wrapper for prepare_agent_concurrent.py.

The checked-in prepare path in this repository snapshot references
manual_goal_utils.normalize_overlay_strategy_imports, but that helper is not
defined.  This wrapper supplies the same no-op normalization used by the prior
scratch diagnostic without modifying repository scripts or official files.
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
SCRIPT_DIR = REPO / ".agents" / "skills" / "vc-proving" / "scripts"
sys.path.insert(0, str(SCRIPT_DIR))

import manual_goal_utils  # noqa: E402


def _noop_normalize_overlay_strategy_imports(_path: Path) -> None:
    return None


manual_goal_utils.normalize_overlay_strategy_imports = _noop_normalize_overlay_strategy_imports
manual_goal_utils.COQC_TRANSIENT_RETRIES = 0
manual_goal_utils.TRANSIENT_COQC_SIGNALS = set()

_original_resolve_coqc_flags = manual_goal_utils.resolve_coqc_flags


def _resolve_coqc_flags_without_project_sources(path: Path):
    project_root, flags = _original_resolve_coqc_flags(path)
    return project_root, [flag for flag in flags if not str(flag).endswith(".v")]


manual_goal_utils.resolve_coqc_flags = _resolve_coqc_flags_without_project_sources

import prepare_agent_concurrent  # noqa: E402


if __name__ == "__main__":
    raise SystemExit(prepare_agent_concurrent.main())
