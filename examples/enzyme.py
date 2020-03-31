#/usr/bin/env python3

"""
Post process the result of enzyme.lean, replacing expanded species with their
original definitions.
"""
import sys

species = [
  ("(ν ?)((Σ#[0.0#.0([]) + 0.1#.(2([]) | 3([]))] | 0.2#.(ν ?)(1([0.0, 0.1, 0.2]))))", "C"),
  ("(ν ?)(1([0.0, 0.1, 0.2]))", "E"),
  ("0([])", "S"),
  ("2([])", "P₁"),
  ("3([])", "P₂"),
]

input = sys.stdin.read()
for pattern, to in species:
  input = input.replace(pattern, to)

print(input)
