# Claude Code Guidelines for PhysLean

## Overall

1. If asked to contniue and have semi-formals or informals just made or mentioned, then work hard on formalizing them.

2. If asked to continue and no obvious work to do, then read through this CLAUDE.md file, go through the code base, and think about expanding to proofs from MTW for GR and proofs for quantum information (both down to basic assumptions progressively up through no-go theorems and other proofs in the literature related to quantum information, thermodynamics to GR, etc.)

## Code Quality

1. **Avoid `sorry`** - Always try to prove lemmas properly. Only use `sorry` as a last resort for genuinely difficult proofs that require significant mathematical machinery not yet available.  Don't leave sorry's that can be proven.  Don't assume something is non-trivial until you try hard.

2. **Use proper imports** - Don't work around missing functionality. Import the appropriate Mathlib modules (e.g., `Mathlib.Analysis.SpecialFunctions.Pow.Real` for `Real.rpow`).

3. **Physics Spirit** - Always ensure you follow the spirit of the physics principles. Never reduce to something simpler, fake, or wrong, just because of errors in build process.  Never give up on doing proper physics, but you can always do a simpler/cleaner approach if that is still 100% not giving up on physics principles.

4. **Research** - You should research online for papers and proofs to help you for complex proofs and to be sure you are following correct physics principles.  Use MCP playwright for accessing web pages that are difficult to fetch directly.

5. **Informal vs. Sorry** - If a proof is too complex to formalize immediately, prioritize writing a clear "Informal Result" (English description within the Lean file) over using a sorry.  However, you must try every effort to convert all informal proofs and sorrys to formal proofs from definitions.

6. **Precision** - You must explicitly identify "physicist's intuition" in a proof and convert it into a rigorous Lean hypothesis. Do not assume a term vanishes or a limit converges just because a textbook implies it; if the proof depends on it, it must be an explicit parameter or hypothesis.

7. **Index Notation** - Use the PhysLean Index Notation system. Do not default to standard Mathlib tensor products if PhysLean has a specific syntax for that physical area. The goal is to make the code readable to "uninitiated" physicists.

8. **Physics Insprired** - While Lean/Mathlib prefer maximum generality, PhysLean prioritizes specific physical models. Do not "over-generalize" a proof if it obscures the physical meaning of a specific model (e.g., the Standard Model gauge groups).

9. **Reals vs. Floats** - When defining physical constants or variables, check if they need to be used in simulations. If a definition is noncomputable, acknowledge it. If the goal is an "interface with programs," prefer computable structures where physically appropriate.

## Organization

1. **New files for new concepts** - Create separate files for new ideas, theorems, or major topics. Keep files focused and modular.

2. **Follow existing patterns** - Match the style and structure of existing PhysLean files (imports, namespaces, documentation format).

3. **Avoid explosion of assumptions** - Ensure you build on top of a foundation of lemmas etc. without making unnecessary explosion of assumptions.  Instead proof the assumptions from foundations.  E.g. avoid `axiom physics_fact : True` type axioms.

4. **Use lemmas alread build** -- Ensure maximum reuse of existing lemmas, theorems, etc. to overall build a deeply connected structure from low level assumptions to high-level theories.

5. **Document physics** - Include docstrings explaining the physical meaning, not just the mathematical definition.

6. **Reference sources** - Cite textbooks (MTW, Wald, etc.) where applicable.

## Lean 4 / Mathlib Proof Standards

You are writing **Lean 4 code** using **mathlib** (and PhysLean if explicitly mentioned).
Your goal is **logical correctness with minimal assumptions**, not creativity.

### Hard constraints (do not violate):

* **Do NOT introduce new axioms**, `axiom`, `sorry`, or `admit` if possible, try very hard to avoid.
* **Do NOT add assumptions** beyond those explicitly stated in the theorem **unless absolutely necessary**.
* If additional assumptions are needed, **stop and explain** why, and propose the **weakest possible ones**.
* **Reuse existing lemmas** from mathlib / PhysLean whenever possible.
* If a lemma likely exists, **search for it conceptually** instead of reproving it.
* **Do NOT hallucinate lemma names**. If unsure, say so.
* Avoid introducing new notation or Unicode symbols unless explicitly requested.
* Prefer short, robust proofs using standard tactics (`simp`, `linarith`, `ring`, `nlinarith`, `aesop`, etc.).
* Avoid unnecessary imports; import only what is required.

### Workflow (high-level):

1. Search: Check if the physical concept exists in the PhysLean hierarchy (e.g., Particles, QFT, Relativity).
2. Syntax Check: Determine if there is custom index notation or Unicode syntax defined for this specific area.
3. Gap Analysis: If a rigorous proof requires a "novelistic" leap from a physics paper, stop and document the missing mathematical link.
4. Staging: If the Lean proof is currently impossible, implement it as an informal_lemma with a detailed English string describing the physical and mathematical requirements.  By try very hard to make formal proofs, especialy if user says so.
5. Refactor Policy: If existing PhysLean code is verbose, apply "Golfing" to align it with Mathlib's concise style, but ensure physical docstrings are preserved.

### Workflow (low-level):
1. **Restate the theorem** in Lean syntax.
2. **List all assumptions** and confirm none are hidden or inflated.
3. **List the key existing lemmas** likely needed (by concept, not guessed names).
4. Only then, **write the Lean proof**.
5. If the proof fails, **explain exactly where and why**, without adding assumptions silently.

### Handling Lean Deterministic Timeouts:

* When a proof times out with Lean's default `maxHeartbeats` (200,000), try increasing the limit progressively:
  - First try `set_option maxHeartbeats 400000 in`
  - If still timing out, try `set_option maxHeartbeats 2000000 in` or even larger (up to 10,000,000)
  - The overall timeout (wall-clock time of ~10 minutes) is the ultimate constraint, not heartbeats
* If a proof still exceeds 10M heartbeats, consider reworking the proof structure:
  - Break complex proofs into helper lemmas
  - Use more explicit intermediate steps
  - Avoid deeply nested case analysis when possible
* Note: Heartbeats are a measure of computational steps, not wall-clock time. A 2M heartbeat proof might take only 20-120 seconds of actual time.

### Additional constraints for PhysLean:

* Prefer **PhysLean definitions** over redefining physics objects.
* Do not assume smoothness, locality, invariance, or convergence unless PhysLean explicitly encodes it.
* If a needed PhysLean lemma does not exist, **mark it clearly** instead of inventing it.
* Treat all "this must cancel" steps as requiring explicit hypotheses.
* Acknowledge Assumptions: Treat physical constants (like Hbar and c) as elements of a specific structure (e.g., HarmonicOscillator) rather than global variables to avoid "assumption explosion."

### building lean

* Only use 1 background build lean job at a time.  Avoid multiple background jobs, because lean uses all cores and that will exhaust the system.

### Commit messages

* Run ./scripts/lint-all.sh and fix all linter issues before committing
* Avoid mentions of claude as coauthor in commit messages (intent is most of direction is human but actual code is claude in all cases, no need to repeat)

### Reviews

* When addressing reviews, respond to any comments, then resolve the issues in code (or respond directly if just question), then mark the comments as resolved.