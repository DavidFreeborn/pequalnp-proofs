# P versus NP participation assessment

Checked on 24 November 2026.

The project coordinates mathematical proof tasks through a public desk. A participant takes a time-limited lease, proves the exact assigned Lean statement in one file, and submits that file as a pull request. The maintainers run their checker and credit accepted contributions to the pull request author.

The implementation supports the central verification claim. CheckLemma.lean reconstructs the recorded statement in an environment containing Mathlib and the project's definitions. It replays project declarations through Lean's kernel, checks the proof's transitive axiom dependencies, and checks that the submitted theorem proves the recorded statement. Its allowed axioms are propext, Classical.choice and Quot.sound. The wrapper pins the toolchain and dependencies, protects the statement bytes, and checks the verifier binary. The authoritative workflow obtains the statement from the public desk rather than the pull request.

This was a source review of the joining client, central checker, relevant build configuration and authoritative workflow, together with representative definitions and proof files. It was not a comprehensive security audit. The reviewed joining client makes requests to pequalnp.com and uses GitHub for public proof submissions. No credential-harvesting behaviour was found in that client.

Formal acceptance establishes a proposition relative to the published definitions and trusted Lean dependencies. It does not establish that the proposition is new, that its informal description is accurate, or that a strategy will resolve P versus NP. The project's first research note explicitly restricts its circuit result to linear bounds for particular graph families and leaves novelty unresolved.

## Session setup

DavidFreeborn/pequalnp-proofs is a public fork of brilliant-hq/pequalnp-proofs. The branch codex/proof-checking contains an isolated GitHub Actions setup because this local command environment cannot resolve external download hosts. Commits made through the connected account use 153205930+DavidFreeborn@users.noreply.github.com.

The workflow installs Lean from its official source, reads the toolchain pin, fetches the pinned Mathlib cache, and builds the project's checker before requesting a task. The verified toolchain is Lean 4.36.0. Its token has read-only repository permissions, checkout does not persist credentials, and the worker has no model API credentials.

The session controller keeps lease identifiers within the runner, renews leases every five minutes, checks candidate proofs with the project's format guard, builds them, and runs the stronger statement checker. Candidate and control files are read from the session directory on codex/proof-checking. The worker is bounded and can release its task and stop through a control record. It is build infrastructure; it does not independently run a language model after the chat stops.

## Assigned mathematical work

The current task is L-meta-3064, a child of L-meta-1678. It asks for a circuit lower bound for the edge function of the Petersen graph with one vertex removed. There are nine input variables and twelve edges:

(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5).

The first gate is fixed as OR(x4,x6). At most thirteen further internal gates are allowed, and the final gate is AND with at most two inputs. The claim is that no such circuit computes the edge function on all inputs. The internal gates may include NOT. The only project import allowed by the desk is PEqualNP.Defs.

A related checked certificate, L-meta-1672, proves a sixteen-gate lower bound when the first gate is AND(x4,x6). It is about 509 KB and includes 147 kernel-evaluated finite checks. L-meta-1912 reconstructs a full circuit around a fixed final AND gate and applies that certificate. Changing the initial AND to OR does not preserve its argument: the gate-elimination and restricted-state certificate depend on the initial operation. Copying the proof and replacing the operation is not justified.

The checked general fifteen-gate lower bound L-meta-2331 is weaker than what this fifteen-gate task needs. L-meta-1908 establishes strong restrictions on the remaining occurrences of x4 and x6 for the OR-first case, but does not itself supply the missing sixteen-gate lower bound.

A direct enumeration of all 512 input assignments gives 58 zero inputs and 454 one inputs. The independence number is four and the minimum vertex-cover number is five. The only minimum covers are {0,2,3,5,6}, {1,2,4,5,8} and {0,1,3,7,8}. A cover containing both 4 and 6 has at least six vertices.

A useful elementary observation is that any nonconstant function implied by the edge function must depend on a vertex cover: if an edge is disjoint from its support, turn on that edge while holding a falsifying support assignment fixed. For a final AND, each nonconstant input function therefore needs such a cover. This helps exclude small circuits, but does not establish the assigned bound for thirteen internal gates with sharing and negation.

No full proof or counterexample has been established in this session. No mathematical pull request has been submitted.

## Additional verification

The example certificate was traced through merged PR 4290 and successful authoritative run 45348787165. Its checker log records acceptance of L-meta-1672, the three allowed axioms, and replay of 3,679 project declarations.

The reproducible script session/small_case_search.py visits 1, 95, 10,449 and 1,315,780 semantic circuit prefixes at depths zero through three after the fixed OR gate. Constants are provided free. It finds no nonconstant function true on every positive target input, so those small cases cannot supply a final AND computing the target. This ordinary Python calculation does not cover the thirteen-gate task and is not a Lean-checked contribution.

There are twelve inclusion-minimal vertex covers, and every pair of vertices belongs to at least one of them. This gives a further structural observation: in any factorisation of the target as f AND g, at least one factor depends on all nine inputs. To see this, suppose f omits u and g omits v. Choose a minimal cover C containing u and v, and set exactly the vertices outside C to true. The edge function is false. Minimality means every vertex of C has a neighbour outside C. Turning on u therefore makes the edge function true, so f was already true because it ignores u. Turning on v likewise shows g was already true. Their AND is then true on the original input, a contradiction. This observation is not a gate-count bound and does not finish the assigned task.

## Lean development outcome

The definitions and three support lemmas in session/FactorSupport.lean were elaborated without errors by Lean 4.36.0 during candidate development. The finite pair-witness lemma uses kernel evaluation. The candidate also proves the empty final-input-list case of the assigned theorem. Its only error is the remaining main gate-count obligation; the build therefore fails and the complete candidate is NOT_ACCEPTED. No claim of desk acceptance is made for these helper lemmas. They have been saved separately so the useful argument can be continued without presenting the unfinished main claim as proved.

## Session close

After working on L-meta-3064 for more than twenty minutes, the task was returned with reason missing_lemma. The controller was instructed to stop after releasing it. The preserved helper argument does not supply the missing quantitative lower bound. Participation setup is complete, but no complete desk task has been accepted. A chat model does not continue doing research once its active session ends.
