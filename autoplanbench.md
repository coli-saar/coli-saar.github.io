---
layout: default
title: "AUTOPLANBENCH: Automatically generating benchmarks for LLM planners from PDDL"
authors:
- name: Katharina Stein
  homepage: https://kastein.github.io/
  affiliation: 1
- name: Alexander Koller
  homepage: https://www.coli.uni-saarland.de/~koller/
  affiliation: 1
affiliations:
- id: 1
  name: Saarland University
paper: https://arxiv.org/abs/2311.09830
code: https://github.com/minecraft-saar/autoplanbench/tree/main
data: https://github.com/minecraft-saar/autoplanbench/tree/main/autoplanbench_dataset
bibtex: |
    @misc{li2023slog,
          title={AutoPlanBench: : Automatically generating benchmarks for LLM planners from PDDL}, 
          author={Katharina Stein and Alexander Koller},
          year={2023},
          eprint={2311.09830},
          archivePrefix={arXiv},
          primaryClass={cs.AI}
    }
---

<center>
    <img src="static/images/autoplanbench/autoplanbench.svg" width="80%" />
</center>


## Abstract

LLMs are being increasingly used for planning-style tasks,
but their capabilities for planning and reasoning are poorly understood.
We present a novel method for automatically converting planning benchmarks written in PDDL
into textual descriptions and offer a benchmark dataset
created with our method.
We show that while the best LLM planners do well on many planning tasks,
others remain out of reach of current methods.


## Contribution 
We present AutoPlanBench, a method for automatically converting PDDL problem specifications into benchmarks for LLMs. AutoPlanBench requires no manual effort for running LLM planning on new domains; the PDDL specification is converted into natural language automatically. This makes it possible, for the first time, to investigate the planning capabilities of LLMs at a larger scale, and it ensures that knowledge that the human problem converter might have about the planning domain doesn't accidentally slip into the natural language task. In addition to the code for converting PDDL into language, we are also releasing an initial set of natural-language conversions of complex PDDL problems from 12 domains.

## Bibtext



