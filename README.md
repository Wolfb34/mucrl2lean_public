# A deep embedding of μCRL in Lean
This repository contains the source code of the project "A Deep Embedding of μCRL in Lean", made as a master thesis for the joint degree Computer Science at the UvA and VU.

μCRL is a process algebra that is used to analyze concurrent processes at a low level. This project formalized concepts from μCRL into Lean, and wrote the Alternating Bit Protocol, a concurrent process, in this formalized μCRL.

# References to the Paper
We will now provide an overview of the source code files containing results mentioned in the paper.

## Section 3.2

* The definition of the μCRL type: ['Lean/mcrl2.lean'](Lean/mcrl2.lean)
* Our initial inductive definition of the equivalence relation: ['Archive/mcrl2_inductive.lean'](Archive/mcrl2_inductive.lean)
* The definition of the transition rules and `seq'`: ['Lean/transition/transition.lean'](Lean/transition/transition.lean)
* The `alt.iff` lemma: ['Lean/transition/iff_lemmas.lean'](Lean/transition/iff_lemmas.lean)
* The `alt.dist` lemma: ['Lean/transition/alt_seq.lean'](Lean/transition/alt_seq.lean)

## Section 3.3

* The definition of bisimulation and bisimilarity: ['Lean/quotient.lean'](Lean/quotient.lean)
* The statement and proofs of the equivalence rules for bisimilarity: ['Lean/quotient.lean'](Lean/quotient.lean)
* The statement and proofs of the congruence rules for alternative and sequential composition: ['Lean/mcrl2_basic/congruence.lean'](Lean/mcrl2_basic/congruence.lean)
* The definition of `R_comp`: ['Lean/quotient.lean'](Lean/quotient.lean)
* The definition of `mcrl2'`: ['Lean/quotient.lean'](Lean/quotient.lean)
* The definition of the `mcrl2_base` class: ['Lean/mcrl2_base/mcrl2_base.lean'](Lean/mcrl2_base/mcrl2_base.lean)
* The `R_add` relation and its lemmas: ['Lean/add.lean'](Lean/add.lean)
* The `mcrl2.alt_dist` and `mcrl2.seq_assoc` lemmas: ['Lean/mcrl2_basic/basic_axioms.lean'](Lean/mcrl2_basic/basic_axioms.lean)
* The base instance for μCRL: ['Lean/mcrl2_basic/mcrl2_basic.lean']

## Section 3.4

* Updated transition rules and `par'`: ['Lean/transition/transition.lean'](Lean/transition/transition.lean)
* The proof from Example 3.4.1: ['Lean/mcrl2_sum/mcrl2_sum.lean'](Lean/mcrl2_sum/mcrl2_sum.lean)

## Section 4

* The `Args` and `Act` types, and the definition of `mul`: ['Lean/ABP/Actions.lean'](Lean/ABP/Actions.lean)
* The mutual recursion version of the ABP : ['Lean/ABP/ABP.lean'](Lean/ABP/ABP.lean)
* The definition of `Step` and `Step.sizeof'`: ['Lean/ABP/ABP.lean'](Lean/ABP/ABP.lean)
* The definition of `ABP` and `ABP_True`: ['Lean/ABP/ABP.lean'](Lean/ABP/ABP.lean)

## Section 5
