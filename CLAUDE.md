# Claude Code Guidelines for PhysLean

## Code Quality

1. **Avoid `sorry`** - Always try to prove lemmas properly. Only use `sorry` as a last resort for genuinely difficult proofs that require significant mathematical machinery not yet available.  Don't leave sorry's that can be proven.

2. **Use proper imports** - Don't work around missing functionality. Import the appropriate Mathlib modules (e.g., `Mathlib.Analysis.SpecialFunctions.Pow.Real` for `Real.rpow`).

3. **Physics Spirit** - Always ensure you follow the spirit of the physics principles. Never reduce to something simpler, fake, or wrong, just because of errors in build process.  Never give up on doing proper physics, but you can always do a simpler/cleaner approach if that is still 100% not giving up on physics principles.

## Organization

1. **New files for new concepts** - Create separate files for new ideas, theorems, or major topics. Keep files focused and modular.

2. **Follow existing patterns** - Match the style and structure of existing PhysLean files (imports, namespaces, documentation format).

3. **Avoid explosion of assumptions** - Ensure you build on top of a foundation of lemmas etc. without making unnecessary explosion of assumptions.  Instead proof the assumptions from foundations.  E.g. avoid `axiom physics_fact : True` type axioms.

4. **Document physics** - Include docstrings explaining the physical meaning, not just the mathematical definition.

5. **Reference sources** - Cite textbooks (MTW, Wald, etc.) where applicable.

## Lean 4 / Mathlib Proof Standards

You are writing **Lean 4 code** using **mathlib** (and PhysLean if explicitly mentioned).
Your goal is **logical correctness with minimal assumptions**, not creativity.

### Hard constraints (do not violate):

* **Do NOT introduce new axioms**, `axiom`, `sorry`, or `admit`.
* **Do NOT add assumptions** beyond those explicitly stated in the theorem **unless absolutely necessary**.
* If additional assumptions are needed, **stop and explain** why, and propose the **weakest possible ones**.
* **Reuse existing lemmas** from mathlib / PhysLean whenever possible.
* If a lemma likely exists, **search for it conceptually** instead of reproving it.
* **Do NOT hallucinate lemma names**. If unsure, say so.
* Avoid introducing new notation or Unicode symbols unless explicitly requested.
* Prefer short, robust proofs using standard tactics (`simp`, `linarith`, `ring`, `nlinarith`, `aesop`, etc.).
* Avoid unnecessary imports; import only what is required.

### Workflow (follow strictly):

1. **Restate the theorem** in Lean syntax.
2. **List all assumptions** and confirm none are hidden or inflated.
3. **List the key existing lemmas** likely needed (by concept, not guessed names).
4. Only then, **write the Lean proof**.
5. If the proof fails, **explain exactly where and why**, without adding assumptions silently.

### Additional constraints for PhysLean:

* Prefer **PhysLean definitions** over redefining physics objects.
* Do not assume smoothness, locality, invariance, or convergence unless PhysLean explicitly encodes it.
* If a needed PhysLean lemma does not exist, **mark it clearly** instead of inventing it.
* Treat all "this must cancel" steps as requiring explicit hypotheses.
