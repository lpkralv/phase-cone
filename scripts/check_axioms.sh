#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

allowed='(propext|Classical[.]choice|Quot[.]sound)'
report="^'[^']+' (does not depend on any axioms|depends on axioms: \[($allowed(, $allowed)*)?\])$"

for check in phase-cone/Check.lean t0-boundary/Check.lean class-one/Check.lean; do
    printf '\n%s\n' "$check"
    if ! output=$(lake env lean "$check" 2>&1); then
        printf '%s\n' "$output" >&2
        exit 1
    fi
    printf '%s\n' "$output"

    # Lean wraps long axiom lists onto indented lines.
    reports=$(printf '%s\n' "$output" | awk '
        /^\047[^\047]+\047 (depends on axioms:|does not depend on any axioms)/ {
            if (line != "") print line
            line = $0
            next
        }
        line ~ /depends on axioms:/ && line !~ /\]$/ && /^[[:space:]]/ {
            sub(/^[[:space:]]+/, "")
            line = line " " $0
            next
        }
        {
            if (line != "") print line
            line = ""
        }
        END { if (line != "") print line }
    ')
    if printf '%s\n' "$reports" | grep -Ev "$report" >/dev/null; then
        printf 'Unexpected axiom or malformed report in %s\n' "$check" >&2
        exit 1
    fi

    expected=$(sed -n 's/^#print axioms //p' "$check")
    actual=$(printf '%s\n' "$reports" | sed -n "s/^'\([^']*\)'.*/\1/p")
    if [[ -z $expected || $actual != "$expected" ]]; then
        printf 'Axiom reports do not match the declarations in %s\n' "$check" >&2
        exit 1
    fi
done
