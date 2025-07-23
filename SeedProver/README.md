# <img src="../imgs/logo.png" height="25"> Seed-Prover: Reasoning wide and deep for Automated Math Theorem Proving

## Overview
In the rapidly evolving landscape of AI, automated theorem proving emerges as a pivotal frontier, seamlessly bridging the rigor of mathematics with powerful LLMs. 
Our system, **Seed Prover**—built on the Lean verifier, leveraging long chain-of-thought reasoning, and powered by a multi-agent inference framework—continuously thinks over a difficult math problem for several days, deeply and widely.

Seed Prover achieved a remarkable milestone by fully solving 4 out of 6 problems in IMO 2025 using 3 days of thinking, achieving a silver medal 🥈 level performance with 30 points (scoring 2/7/7/7/7/0 across the six problems by the IMO board).
Beyond its IMO success, Seed Prover has set the new state-of-the-art for formal mathematical reasoning across multiple benchmarks:
- 100% success rate on MiniF2F-valid
- 99% on MiniF2F-test
- 79% on formalized past IMO problems (including 2024 P1, P2, P4)
- 30% on combinatorics problems in CombiBench
- 50% on PutnamBench
- 82% on MiniCTX-v2

## IMO 2025
Seed Prover solved 4 out of 6 problems in IMO 2025, with the following breakdown:
- **Day 1**: Fully solved P2 (geometry) and P3 (number theory)
- **Day 2**: Fully solved P4 (number theory) and P5 (combinatorics / algebra)

### Details
- P1 (combinatorics) [Lean](imo2025/p1.lean) : Fully proved after the competion, this is not scored by the IMO.
- P2 (geometry) [NL](imo2025/p2_proof.pdf) : Generated and verified in 2 seconds using Seed-Geometry system
- P3 (number theory) [NL](imo2025/p3_proof.pdf) [Lean](imo2025/p3.lean): Solved in 3 days, with a 2000-line formal proof
- P4 (number theory) [NL](imo2025/p4_proof.pdf) [Lean](imo2025/p4.lean): Solved in 3 days, with a 4000-line formal proof
- P5 (combinatorics / algebra) [NL](imo2025/p5_proof.pdf) [Lean](imo2025/p5.lean): Solved in 1 day, with a proof slightly different from known human solutions

P3,4,5 are compiled under Lean v4.14.0.

## Test-time Scaling of Seed Prover
The success of Seed Prover stems from multi-stage RL training (enhancing long chain-of-thought reasoning and Lean interaction) and innovative test-time scaling strategies:

### Light
- Iteratively refines proofs using Lean compiler feedback with self-summarization, overcoming single-pass inference token budgets
- Refines each proof at most 8–16 times (Pass@8–16), completing within an hour
- Example: Proved IMO 2022 P2 (MOHS=15) under this setting (would require Pass@8192 without refinement)

### Medium
- Combines inner and outer refinement processes:
  - Outer refinement: Same as Light setting (refines proof of original problem)
  - Inner refinement: Proves difficult lemmas that outer refinement fails to resolve
- Handles longer, more complex proofs (over 1000 lines of code)
- Runs from hours to days
- Examples: Solved IMO 2003 P6 (MOHS=35) and IMO 2025 P5

### Heavy
- Enables "wide thinking" by exploring problem properties through conjecture and lemma pools
- Proves/disproves conjectures, with a proposer creating new conjectures to tackle hard ones
- After days of thinking, pools contain thousands of math facts
- Top-scoring lemmas (by proof rate and relatedness) assist in final proof
- Examples: Solved IMO 2025 P3 and P4


## Performance Results
Seed Prover sets new state-of-the-art across multiple formal reasoning benchmarks:

| Metric               | Seed Prover                              | Previous SOTA                     |
|----------------------|------------------------------------------|-----------------------------------|
| IMO 2025             | 4/6 (Heavy), 30 points 🥈                | 5/6 (Natural language, OpenAI)   |
| Past IMO             | 79% (Heavy)                              | -                                 |
| MiniF2F-valid        | 100% (Medium; 1 problem uses Heavy)      | 90.6% (DeepSeek-Prover-V2)        |
| MiniF2F-test         | 99%, 243/244 (Medium)                    | 92.2% (Kimina-Prover)             |
| PutnamBench          | 331/657 (Medium)                         | 64/657 (Goedel-Prover-V2)         |
| CombiBench           | 30% (Medium)                             | 10% (Deepseek-Prover-V2)          |
| MiniCTX-v2           | 81.8% (Light)                            | 44.3% (O4-mini)                   |

These results demonstrate Seed Prover's adaptability across high school competitions, advanced math concepts, and diverse mathematical domains.


## Citation
TBA.
