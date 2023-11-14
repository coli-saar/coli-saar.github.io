---
layout: default
title: "SLOG: A Structural Generalization Benchmark for Semantic Parsing"
authors:
- name: Bingzhi Li
  affiliation: 1
- name: Lucia Donatelli
  affiliation: 2
- name: Alexander Koller
  homepage: https://www.coli.uni-saarland.de/~koller/
  affiliation: 3
- name: Tal Linzen
  affiliation: 4
- name: Yuekun Yao
  affiliation: 3
- name: Najoung Kim
  affiliation: 5
affiliations:
- id: 1
  name: Universite Paris Cite
- id: 2
  name: Vrije Universiteit Amsterdam
- id: 3
  name: Saarland University
- id: 4
  name: New York University
- id: 5
  name: Boston University
paper: https://arxiv.org/abs/2310.15040
code: https://github.com/bingzhilee/SLOG
data: https://github.com/bingzhilee/SLOG
sections:
- title: Abstract
  content: |
    The goal of compositional generalization benchmarks is to evaluate how well models generalize to new complex linguistic expressions. Existing benchmarks often focus on lexical generalization, the interpretation of novel lexical items in syntactic structures familiar from training; structural generalization tasks, where a model needs to interpret syntactic structures that are themselves unfamiliar from training, are often underrepresented, resulting in overly optimistic perceptions of how well models can generalize. We introduce SLOG, a semantic parsing dataset that extends COGS (Kim and Linzen, 2020) with 17 structural generalization cases. In our experiments, the generalization accuracy of Transformer models, including pretrained ones, only reaches 40.6%, while a structure-aware parser only achieves 70.8%. These results are far from the near-perfect accuracy existing models achieve on COGS, demonstrating the role of SLOG in foregrounding the large discrepancy between models' lexical and structural generalization capacities.
- title: Section Two
  content: |
    This is just a test paragraph.

    Here's a second paragraph to that test paragraph.
---

@misc{li2023slog,
      title={SLOG: A Structural Generalization Benchmark for Semantic Parsing}, 
      author={Bingzhi Li and Lucia Donatelli and Alexander Koller and Tal Linzen and Yuekun Yao and Najoung Kim},
      year={2023},
      eprint={2310.15040},
      archivePrefix={arXiv},
      primaryClass={cs.CL}
}
