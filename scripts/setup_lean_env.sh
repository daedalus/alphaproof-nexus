#!/usr/bin/env bash
# setup_lean_env.sh — Set up the Lean 4 environment for AlphaProof Nexus
#
# Usage:
#   source scripts/setup_lean_env.sh    # activate env in current shell
#   bash scripts/setup_lean_env.sh      # print instructions

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# ── 1. Check Lean toolchain ──────────────────────────────────────────────
REQUIRED_LEAN="leanprover/lean4:v4.30.0-rc2"
TOOLCHAIN=$(cat "$PROJECT_ROOT/lean-toolchain" 2>/dev/null || echo "")

if [ "$TOOLCHAIN" != "$REQUIRED_LEAN" ]; then
  echo "⚠  Expected toolchain $REQUIRED_LEAN in lean-toolchain"
  echo "   Found: $TOOLCHAIN"
fi

if ! command -v lean &>/dev/null; then
  echo "✖  'lean' not found on PATH."
  echo "   Install elan: curl -sSf https://leanprover-community.github.io/getelan.py | python3"
  echo "   Then run: elan toolchain install $REQUIRED_LEAN"
  exit 1
fi

LEAN_VERSION=$(lean --version 2>/dev/null | head -1 || echo "unknown")
echo "✓  lean: $LEAN_VERSION"

# ── 2. Check lake ────────────────────────────────────────────────────────
if ! command -v lake &>/dev/null; then
  echo "✖  'lake' not found on PATH (should be installed with elan)"
  exit 1
fi

LAKE_VERSION=$(lake --version 2>/dev/null | head -1 || echo "unknown")
echo "✓  lake: $LAKE_VERSION"

# ── 3. Check Mathlib dependencies ────────────────────────────────────────
if [ ! -d "$PROJECT_ROOT/.lake/packages/mathlib" ]; then
  echo "   Mathlib not cached — running 'lake build' to fetch dependencies..."
  cd "$PROJECT_ROOT"
  lake build 2>&1 | tail -5
fi
echo "✓  Mathlib: $(cd "$PROJECT_ROOT/.lake/packages/mathlib" && git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"

# ── 4. Build ErdosLib (the shared library) ───────────────────────────────
if [ ! -f "$PROJECT_ROOT/.lake/build/lib/lean/ErdosLib.olean" ]; then
  echo "   Building ErdosLib (this compiles Mathlib on first run, may take a while)..."
  cd "$PROJECT_ROOT"
  lake build ErdosLib 2>&1
fi
echo "✓  ErdosLib built"

# ── 5. Compile verification ──────────────────────────────────────────────
echo ""
echo "── Verifying compilation ──"
cd "$PROJECT_ROOT"
for f in \
  ErdosLib/proven/Tiling.lean \
  ErdosLib/proven/GeometricTiling.lean \
  Erdos634/population/member_07_gen7_geometric_obstruction.lean \
  Erdos25-evolve/population/member_04_gen1_head_truncation.lean \
  Erdos1/population/member_05_champion.lean
do
  if [ -f "$f" ]; then
    if lake env lean "$f" &>/dev/null; then
      echo "  ✓  $f"
    else
      echo "  ✖  $f (errors — run 'lake env lean $f' to inspect)"
    fi
  fi
done

echo ""
echo "── Environment ready ──"
echo "  Compile any file:  lake env lean <filename>"
echo "  List targets:      lake build"
echo "  Build library:     lake build ErdosLib"
