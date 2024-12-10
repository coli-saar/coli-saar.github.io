---
layout: default
title: "Automating the Generation of Prompts for LLM-based Action Choice in PDDL Planning <br>(AutoPlanBench 1.0)"
authors:
- name: Katharina Stein
  homepage: https://kastein.github.io/
  affiliation: 1
- name: Daniel Fiser
  homepage: https://www.danfis.cz/
  affiliation: 1
- name: Joerg Hoffmann
  homepage: http://fai.cs.uni-saarland.de/hoffmann/
  affiliation: 1
- name: Alexander Koller
  homepage: https://www.coli.uni-saarland.de/~koller/
  affiliation: 1
affiliations:
- id: 1
  name: Saarland University
paper: https://github.com/coli-saar/coli-saar.github.io/blob/main/static/images/autoplanbench/AutoPlanBench_PRL_Camera-ready.pdf
code: https://github.com/minecraft-saar/autoplanbench/releases/tag/v1.0
data: https://github.com/minecraft-saar/autoplanbench/tree/main/autoplanbench_dataset
bibtex: |
    @misc{stein2024autoplanbench,
          title={AutoPlanBench: Automatically generating benchmarks for LLM planners from PDDL}, 
          author={Katharina Stein and Daniel Fi\v{s}er and J\"org Hoffmann and Alexander Koller},
          year={2024},
          eprint={2311.09830v2},
          archivePrefix={arXiv},
          primaryClass={cs.AI}
    }
---

<center>
    <img src="static/images/autoplanbench/autoplanbench2.png" width="50%" />
</center>


**Note on different versions**: <br>
This website corresponds to the version of the paper that has been presented at the [Workshop on Bridging the Gap Between AI Planning and Reinforcement Learning](https://prl-theworkshop.github.io/prl2024-icaps/) (PRL) at ICAPS 2024. The workshop version of the paper can be accessed using their website or the link above. <br>

The newest version of the paper with an extended dataset (Autoplanbench 2.0) is available at a [separate website](https://coli-saar.github.io/autoplanbench).<br>

A previous version of this paper had been published on Arxiv under the title ["AutoPlanBench: Automatically generating benchmarks for LLM planners from PDDL"](https://arxiv.org/abs/2311.09830). <br> 

## AutoPlanBench

We present **AutoPlanBench**, a tool for **automatically converting classical planning benchmarks from PDDL into natural language** planning tasks. PDDL (Planning Domain Definition Language) planning domains are very popular in the classical AI planning research community and available domains differ with respect to a number of characteristics designed to compare the performance classical planning approaches in different settings.

AutoPlanBench makes these planning tasks available for research on **reasoning and planning with Large Language Models** (LLMs) at a large scale without requiring manual effort or detailed knowledge about PDDL and the domains. We show that the automatically converted planning domains **yield comparable results as manually created** domain descriptions (from Valmeekam et al. 2023: [PlanBench](https://github.com/karthikv792/LLMs-Planning/tree/main/plan-bench)) across different planning domains and LLM planning approaches.
Evaluating LLM planners across a broad range of planning domains, enables us to pinpoint features of planning domains and specific planning problems that make them hard to for LLMs. 

We release the dataset of natural-language conversions of 12 PDDL domains and a small set of NL planning problems for each of them. Additionally, we provide the code for converting more PDDL domains and problems into natural-language planning tasks for LLMs. 

In addition to the code for creating LLM planning problems, we provide the implementation of four different LLM planning approaches as well as the code to automatically generating few-shot examples for these approaches. 


## PDDL to NL Planning Problems

PDDL planning tasks consist of a domain file and a problem file that defines a specific problem instance with respect to the domain. AutoPlanBench converts both the domain PDDL file and problem files into natural language encodings as illustrated below. The details about the LLM-based conversion methodology can be found in our paper.  

**Blocksworld Domain**
<details open>
<summary> 
Blocksworld Example
</summary>

<img src="static/images/autoplanbench/blocksworld_domain_conv.png" width="70%" />


<br>
<br>

<img src="static/images/autoplanbench/blocksworld_problem_conv.png" width="70%" />

</details>

**Visitall Domain**
<details>
<summary>Visitall Example</summary>

<img src="static/images/autoplanbench/visitall_domain_conv.png" width="70%" />


<br>
<br>

<img src="static/images/autoplanbench/visitall_problem_conv.png" width="70%" />

</details>

## LLM Action-Choice Mechanisms

### Overall Set-up

<img src="static/images/autoplanbench/setup.png" width="50%" />

* **P-LLM**: does the action selection, i.e. predicts a complete plan / the next action given the domain and problem descriptions
* **L-LLM**: translates natural language output of the P-LLM back to PDDL
* **Simulator**: simulates the world state; outputs an observation for an input action; checks plan validity; determines whether the goal is satisfied

### Tested Approaches

|                 | Plan Generation (Non-interactive)                                                                  | LLM as a policy (Interactive)                                                                                                                                  |
|-----------------|----------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------|
| **No Thoughts** | *Basic* <br> * one complete plan                                                                   | *Act* <br> * step by step prediction of next action <br> * observation from the simulator                                                    |
| **Thoughts**    | *CoT* <br> * Chain-of-Thought (Wei et al. 2022) <br> * one complete plan <br> * reasoning thoughts | *ReAct* <br> * Yao et al. 2023 <br> * step by step prediction of next action <br> * observation from the simulator <br> * reasoning thoughts |

<details>
  <summary>Full ReAct Example</summary>
  <img src="static/images/autoplanbench/interactive_example/prompt.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step1.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step2.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step3.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step4.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step5.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step6.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step7.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step8.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step9.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step10.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step11.png" width="70%" />
  <img src="static/images/autoplanbench/interactive_example/step12.png" width="70%" />
  

</details>


## Experiments and Results 

**Metrics**<br>
* Coverage: The absolute number of correctly solved instances
    * Plan generation: an instance is considered to be solved correctly in case the goal is satisfied after executing all predicted actions from the generated plan
    * Policy: an instance is considered to be solved correctly in case the goal is satisfied within the specified number of steps; the simulator itself takes care of stopping the generation of further actions in that case


**Symbolic Baselines**<br>
* rnd: selects an action at random from all actions applicable in the current state 
* BrFS: Breadth-first search
* lmc: optimal A* and the LM-Cut heuristic (Helmert et al. 2009)
* ff: satisficing greedy best-first search with FF heuristic (Hoffmann and Nebel, 2001)
We restrict the number of selected actions for rnd to the same number as the maximum number of steps for the LLM policy mechanisms. <br>
For the other three baselines we impose a memory and time limit of 8 GB and 30 minutes respectively. 


**Results: AutoPlanBench vs. Manual Conversions**<br>
We find that the automatically converted planning domains (Auto) yield comparable results as manually created domain descriptions (Manual; from Valmeekam et al. 2023: [PlanBench](https://github.com/karthikv792/LLMs-Planning/tree/main/plan-bench)) across the different planning domains and LLM action-choice mechanisms. 

<img src="static/images/autoplanbench/results_version1/comparison_table.png" width="80%" />


**Results: LLM Action-choice Performance**<br>
Overall, we find that the planning performance differs considerably between the 12 tested domains. While the best LLM action-choice performance (ReAct) do well on some planning tasks, many remain out of reach of current search-based planning methods.

<img src="static/images/autoplanbench/results_version1/main_results_table.png" width="80%" />

One potential factor influencing the different results across domains is the plan length. Overall, the LLM planners performed better on domains with shorter problems. This could indicate that LLMs are worse at long-term planning or at generalization from shorter demonstrations to larger test problems. 

We find that domains with actions that have irreversible effects on the state and where hence dead-end states can occur pose a problem for LLM planners (Floortile, Goldminer).

## Results: Scaling Experiments


<img src="static/images/autoplanbench/results_version1/scaled_results_table.png" width="80%" />



## References

M. Helmert and C. Domshlak. Landmarks, critical paths and abstractions: What’s the difference anyway? In *Proceedings of the 19th International Conference on Automated Planning and Scheduling, ICAPS*. AAAI, 2009.<br>
J. Hoffmann and B. Nebel. The FF planning system: Fast plan generation through heuristic search. 'Journal of Artificial Intelligence Research*, 14:253–302, 2001.<br>
K. Valmeekam, M. Marquez, A. Olmo, S. Sreedharan, and S. Kambhampati. Planbench: An extensible benchmark for evaluating large language models on planning and reasoning about change. In *Thirty-seventh Conference on Neural Information Processing Systems Datasets and Benchmarks Track*, 2023.<br>
K. Valmeekam, M. Marquez, S. Sreedharan, and S. Kambhampati. On the planning abilities of large language models - a critical investigation. In *Advances in Neural Information Processing Systems*, pages 75993– 76005. Curran Associates, Inc., 2023.<br>
J. Wei, X. Wang, D. Schuurmans, M. Bosma, b. ichter, F. Xia, E. Chi, Q. V. Le, and D. Zhou. Chain-of-thought prompting elicits reasoning in large language models. In *Advances in Neural Information Processing Systems*, volume 35, pages 24824–24837. Curran Associates, Inc., 2022.<br>
S. Yao, J. Zhao, D. Yu, N. Du, I. Shafran, K. R. Narasimhan, and Y. Cao. React: Synergizing reasoning and acting in language models. In *The Eleventh International Conference on Learning Representations*, 2023.


