---
layout: default
title: "Exploring Graph Representations of Logical Forms for Language Modeling"
authors:
- name: Michael Sullivan
  homepage: https://mjs227.github.io/home/
  affiliation: 1, 2
affiliations:
- id: 1
  name: Saarland University
- id: 2
  name: University at Buffalo
paper: https://arxiv.org/pdf/2505.14523
code: https://github.com/mjs227/GFoLDS
bibtex: |
    @article{sullivan2025exploring,
          title={Exploring Graph Representations of Logical Forms for Language Modeling},
          author={Sullivan, Michael},
          journal={arXiv preprint arXiv:2505.14523},
          year={2025}
    }
---

<center>
    <img src="static/images/gfolds/dmrs_ex.png" width="50%" />
</center>

# Abstract

We make the case for language models over logical forms (LFLMs), arguing that such models are more data-efficient than their textual counterparts. To that end, we introduce the *<ins>G</ins>raph-based <ins>Fo</ins>rmal-<ins>L</ins>ogical <ins>D</ins>istributional <ins>S</ins>emantics* (GFoLDS) prototype, a pretrained LM over graph representations of logical forms, as a proof-of-concept of LFLMs. Using GFoLDS, we present strong experimental evidence that LFLMs can leverage the built-in, basic linguistic knowledge inherent in such models to immediately begin learning more complex patterns. On downstream tasks, we show that GFoLDS vastly outperforms textual, transformer LMs pretrained on similar amounts of data, indicating that LFLMs can learn with substantially less data than models over plain text. Furthermore, we show that the performance of this model is likely to scale with additional parameters and pretraining data, suggesting the viability of LFLMs in real-world applications.


# Why Logical Forms?

We argue that there are two main advantages of LFLMs versus models over plain text, that allow them to learn from less data:

1. The function-argument structure of logical forms has a syntactic equivalence-classing/de-noising effect: all syntactic paraphrases of the same proposition&mdash;for example, an active sentence and its passive counterpart&mdash;are mapped to the same representation. This means that an LFLM does not need to learn to equate periphrastic structures, so it can immediately begin learning co-occurrence relations between predicates.

2. (Some) logical-form representation frameworks include morphosyntactic features such as number, tense, person, etc. This further de-noises the model’s input by offloading the morphological realization of these properties to explicitly annotated labels. This is to say that an LFLM does not need to learn the surface patterns corresponding to inflection, because this information is explicitly provided. For example, an LM over logical forms does not need to learn that the suffix *–s* denotes aplural noun&mdash;or irregular realizations of pluralization, e.g. *goose*/*geese*&mdash;because plural nouns are directly labeled as such.
