# Claude Code Guidelines for PhysLean

## Code Quality

1. **Avoid `sorry`** - Always try to prove lemmas properly. Only use `sorry` as a last resort for genuinely difficult proofs that require significant mathematical machinery not yet available.

2. **Use proper imports** - Don't work around missing functionality. Import the appropriate Mathlib modules (e.g., `Mathlib.Analysis.SpecialFunctions.Pow.Real` for `Real.rpow`).

## Organization

3. **New files for new concepts** - Create separate files for new ideas, theorems, or major topics. Keep files focused and modular.

4. **Follow existing patterns** - Match the style and structure of existing PhysLean files (imports, namespaces, documentation format).

## Documentation

5. **Document physics** - Include docstrings explaining the physical meaning, not just the mathematical definition.

6. **Reference sources** - Cite textbooks (MTW, Wald, etc.) where applicable.
