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
    <img src="static/images/autoplanbench/autoplanbench2.png" width="70%" />
</center>



## AutoPlanBench

We present AutoPlanBench, a tool for automatically converting classical planning benchmarks from PDDL (Planning Domain Definition Language) into natural language planning tasks. PDDL planning domains are very popular in the classical AI planning research community and available domains differ with respect to a number of characteristics designed to compare the performance classical planning approaches in different settings.

AutoPlanBench makes these planning tasks available for research on reasoning and planning with Large Language Models (LLMs) at a large scale without requiring manual effort or detailed knowledge about PDDL and the domains. 
Evaluating LLM planners across such a broad range of planning domains, enables us to pinpoint features of planning domains and specific planning problems that make them hard to for LLMs. 

We release the dataset of natural-language conversions of 12 PDDL domains and a small set of NL planning problems for each of them. Additionally, we provide the code for converting more PDDL domains and problems into natural-language planning tasks for LLMs. 

In addition to the code for creating LLM planning problems, we provide the implementation of four different LLM planning approaches as well as the code to automatically generating few-shot examples for these approaches. 


## PDDL to NL Methodology

<center>
    <img src="static/images/autoplanbench/blocksworld_domain_conv.png" width="70%" />
</center>

<center>
    <img src="static/images/autoplanbench/blocksworld_problem_conv.png" width="70%" />
</center>

<center>
    <img src="static/images/autoplanbench/visitall_domain_conv.png" width="70%" />
</center>

<center>
    <img src="static/images/autoplanbench/visitall_problem_conv.png" width="70%" />
</center>

## LLM Planning Approaches

## LLM Planning Results 

In LLM planning experiments on a new suite of 12 planning domains, we find that the planning performance differs considerably between the domains. We show that while the best LLM planners do well on some planning tasks, many remain out of reach of current search-based planning methods.


